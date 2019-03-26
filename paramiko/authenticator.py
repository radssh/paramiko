"""
High level authentication logic module.

Largely replaces what used to be implemented solely within `SSHClient` and its
``_auth()`` method.

Technically, this module's main API member - `Authenticator` - sits below
`SSHClient` (meaning it can be used by non-Client-based code) and above
`Transport` (which provides the bare auth SSH message 'levers' only.)

.. note::
    This is not to be confused with the `paramiko.auth_handler` module, which
    sits *below* (or within) `Transport`, handling the low level guts of
    submitting authentication protocol messages and awaiting their responses.
"""
import getpass
import hashlib
import os
import re
import sys
import traceback
import binascii

try:
    import Queue
    from StringIO import StringIO
except ImportError:
    import queue as Queue
    from io import StringIO

from paramiko.pkey import PKey
from paramiko.rsakey import RSAKey
from paramiko.dsskey import DSSKey
from paramiko.ecdsakey import ECDSAKey
from paramiko.ed25519key import Ed25519Key
from paramiko.agent import Agent
from paramiko.message import Message
from paramiko.common import (
    cMSG_SERVICE_REQUEST, cMSG_DISCONNECT, DISCONNECT_SERVICE_NOT_AVAILABLE,
    DISCONNECT_NO_MORE_AUTH_METHODS_AVAILABLE, cMSG_USERAUTH_REQUEST,
    cMSG_SERVICE_ACCEPT, DEBUG, AUTH_SUCCESSFUL, INFO, cMSG_USERAUTH_SUCCESS,
    cMSG_USERAUTH_FAILURE, AUTH_PARTIALLY_SUCCESSFUL,
    cMSG_USERAUTH_INFO_REQUEST, DEBUG, ERROR, WARNING, INFO,
    AUTH_FAILED, cMSG_USERAUTH_PK_OK, MSG_USERAUTH_PK_OK,
    cMSG_USERAUTH_INFO_RESPONSE, MSG_SERVICE_REQUEST, MSG_SERVICE_ACCEPT,
    MSG_USERAUTH_REQUEST, MSG_USERAUTH_SUCCESS, MSG_USERAUTH_FAILURE,
    MSG_USERAUTH_BANNER, MSG_USERAUTH_INFO_REQUEST, MSG_USERAUTH_INFO_RESPONSE,
    cMSG_USERAUTH_GSSAPI_RESPONSE, cMSG_USERAUTH_GSSAPI_TOKEN,
    cMSG_USERAUTH_GSSAPI_MIC, MSG_USERAUTH_GSSAPI_RESPONSE,
    MSG_USERAUTH_GSSAPI_TOKEN, MSG_USERAUTH_GSSAPI_ERROR,
    MSG_USERAUTH_GSSAPI_ERRTOK, MSG_USERAUTH_GSSAPI_MIC, MSG_NAMES,
    cMSG_USERAUTH_BANNER, MSG_USERAUTH_INFO_REQUEST, cMSG_USERAUTH_INFO_RESPONSE
)
from paramiko.ssh_exception import AuthenticationException
from paramiko.ssh_gss import GSSAuth, GSS_EXCEPTIONS

class Authenticator(object):
    """
    Wraps a `Transport` and uses it to authenticate or die trying.

    Lifecycle is relatively straightforward:

    - Instantiate with a handle onto a `Transport` object. This object must
      already have been prepared for authentication by calling
      `Transport.start_client`.
    - Call the instance's `authenticate_with_kwargs` method with as many or few
      auth-source keyword arguments as needed, which will:
        - attempt to authenticate in a documented order of preference
        - if successful, return an `AuthenticationResult`
        - if unsuccessful or if additional auth factors are required, raise an
          `AuthenticationException` (or subclass thereof) which will exhibit a
          ``.result`` attribute whose value is an `AuthenticationResult`.
        - either way, the point is that the caller will have access to an
          `AuthenticationResult` object exposing the various auth sources
          tried, what order they were tried in, and what the result was.
        - see API docs for `authenticate` for further details.
    - Alternately, for tighter control of which auth sources are tried and in
      what order, call `authenticate` directly (it's what implements the guts
      of `authenticate_with_kwargs`) which foregoes most kwargs in lieu of an
      iterable containing `AuthSource` objects.
    """
    service_name = "ssh-userauth"

    # Default settings for authentication options, in the style of
    # OpenSSH config. Can be updated from dict options from SSHConfig.lookup()
    # or from a manually constructed dict.
    # Differences from OpenSSH defaults:
    # - BatchMode defaults to 'yes' instead of 'no'
    ssh_config = {
        "gssapiauthentication": "no",
        "hostbasedauthentication": "no",
        "pubkeyauthentication": "yes",
        "kbdinteractiveauthentication": "yes",
        "passwordauthentication": "yes",
        "challengeresponseauthentication": "yes",
        "preferredauthentications": "gssapi-with-mic,hostbased,publickey,keyboard-interactive,password",
        "user": getpass.getuser(),
        "batchmode": "yes",
        "identityfile": [],
        "certificatefile": [],
        "enablesshkeysign": "no",
        "fingerprinthash": "sha256",
        "gssapidelegatecredentials": "no",
        # "hostbasedkeytypes": "",
        "identitiesonly": "no",
        "kbdinteractivedevices": "",
        "numberofpasswordprompts": "3",
        # "pkcs11provider": "", # TBD
        # "pubkeyacceptedkeytypes": "",
    }

    def __init__(self, transport, username=None,
            default_password='', keyfile_or_key=None, passphrase='',
            auth_timeout=15):
        # TODO: probably sanity check transport state and bail early if it's
        # not ready.
        # TODO: consider adding some more of SSHClient.connect (optionally, if
        # the caller didn't already do these things) like the call to
        # .start_client; then update lifecycle in docstring.
        self.transport = transport
        self._log = transport._log
        self.username = username or self.ssh_config["user"]
        if default_password:
            self.password_list = [default_password]
        else:
            self.password_list = []
        self.default_password = default_password
        if keyfile_or_key:
            self.key_list = [keyfile_or_key]
        else:
            self.key_list = []
        self.passphrase = passphrase
        # Time to wait for server reply (for each send, not total time)
        self.auth_timeout = auth_timeout
        # State of authentication
        self.server_reply = Queue.Queue()
        self.authenticated = False
        self.in_progress = False
        # Temporary, for backward compatibility with legacy AuthHandler
        self._handler_table = {}

    def update_authentication_options(self, d):
        """
        SSHConfig.lookup() or manually constructed dict
        Lists will be extended with updated values
        Values starting with + or - will append or subtract from a
        comma-separated string
        Other values will be substituted in whole
        """
        for k, v in d.items():
            if k not in self.ssh_config:
                continue
            if isinstance(v, list):
                self.ssh_config[k].extend(v)
            elif v.startswith('+'):
                val = self.ssh_config[k].split(",")
                val.extend(v[1:].split(","))
                self.ssh_config[k] = ",".join(val)
            elif v.startswith("-"):
                val = self.ssh_config[k].split(",")
                for subtract in val.extend(v[1:].split(",")):
                    try:
                        val.remove(subtract)
                    except ValueError:
                        pass
                self.ssh_config[k] = ",".join(val)
            else:
                self.ssh_config[k] = v
        self._log(DEBUG, self.ssh_config)

    def queue_server_response(self, ptype, m):
        # Used by Transport thread to pass messages from server
        # to the running authentication thread.
        self.server_reply.put((ptype, m))

    def is_authenticated(self):
        return self.authenticated

    def abort(self):
        # Something bad happened at the transport layer
        if self.in_progress:
            # Fabricate a failure message with a bogus list of methods that may
            # continue, so we don't block on reading response that might not
            # get delivered, due to disconnect.
            m = Message()
            m.add_string("disconnected")
            m.add_boolean(False)
            m.rewind()
            self.queue_server_response(MSG_USERAUTH_FAILURE, m)
            self.in_progress = False

    def authenticate_with_kwargs(self, lots_o_kwargs_here):
        # Basically SSHClient._auth signature...then calls
        # sources_from_kwargs() and stuffs result into authenticate()?
        # TODO: at the start, just copypasta/tweak SSHClient._auth so the
        # break-up is tested; THEN move to the newer cleaner shit?
        # TODO: this is probably a good spot to reject the
        # password-as-passphrase bit; accept distinct kwargs and require
        # SSHClient to implement the fallback on its end.
        pass

    def authenticate(self, force_service_request=False, explicit_methods=None):
        # TODO: define AuthSource (maybe rename...lol), should be lightweight,
        # pairing an auth type with some value or iterable of values
        # TODO: implement cleaner version of SSHClient._auth, somehow, that
        # handles multi-factor auth much better than the current shite
        # trickledown. (Be very TDD here...! Perhaps wait until single-source
        # tests all pass first, then can ensure they continue to do so?)
        if explicit_methods:
            self.available_methods = explicit_methods
        else:
            # Assemble a MFA-capable dict of method names with iterators
            # for various AuthMethod objects to attempt, according to
            # what the server passes back in the MSG_USERAUTH_FAILURE content.
            self.available_methods = {}
            if self.password_list:
                self.available_methods["password"] = AuthPassword.factory(self, *self.password_list)
            self.available_methods["publickey"] = AuthPublicKey.factory(self, *self.key_list)
            self.available_methods["keyboard-interactive"] = AuthKeyboardInteractive.factory(self, ('Password(?i)', 'bongo'))
            self.available_methods["gssapi-with-mic"] = AuthGSSAPI.factory(self)

        self.transport.lock.acquire()
        try:
            if not self.in_progress or force_service_request:
                # Send a MSG_SERVICE_REQUEST for ssh-userauth, and expect
                # server to reply with MSG_SERVICE_ACCEPT
                self._log(DEBUG, "Requesting {}".format(self.service_name))
                m = Message()
                m.add_byte(cMSG_SERVICE_REQUEST)
                m.add_string(self.service_name)
                self.transport._send_message(m)
                # Server expected to reply with MSG_SERVICE_ACCEPT
                resp = self.server_reply.get(timeout=self.auth_timeout)
                ptype, m = resp
                if ptype != MSG_SERVICE_ACCEPT:
                    raise AuthenticationException("Expected cMSG_SERVICE_ACCEPT(6), but got {:d}".format(ptype))
                service_name = m.get_text()
                if service_name !=  self.service_name:
                    raise AuthenticationException("Unexpected service name: expected {}, got {}".format(self.service_name, service_name))
                self._log(DEBUG, "Server accepted {} request".format(self.service_name))
                self.in_progress = True
                current_auth = AuthNone(self)
                self.transport._send_message(current_auth.message())
                self._log(DEBUG, "Sent auth-none")
            else:
                self._log(DEBUG, "Resuming {} processing".format(self.service_name))
                current_auth = "placebo"
                raise NotImplemented

            while self.in_progress:
                ptype, m = self.server_reply.get(timeout=self.auth_timeout)
                self._log(DEBUG, "Got reply from server: {:d}".format(ptype))

                if ptype == MSG_USERAUTH_SUCCESS:
                    self._log(INFO, "Authentication success!")
                    self.authenticated = True
                    self.in_progress = False
                    break
                elif ptype == MSG_USERAUTH_BANNER:
                    banner = m.get_text()
                    language = m.get_text()
                    self._log(DEBUG, "Banner received: {} ({})".format(banner.strip(), language))
                    self.transport.banner = banner
                    continue
                elif ptype == MSG_USERAUTH_FAILURE:
                    server_accepts = m.get_text().split(',')
                    partial_success = m.get_boolean()
                    if partial_success:
                        self._log(INFO, "Authentication {} partial success".format(current_auth))
                    else:
                        self._log(INFO, "Authentication {} failed".format(current_auth))
                    self._log(DEBUG, "Authentications that can continue: {}".format(",".join(server_accepts)))
                else:
                    # Anything other than general authentication messages should
                    # be handled by the specific AuthMethod object
                    try:
                        continue_message = current_auth.additional_info(ptype, m)
                        if continue_message:
                            self._log(DEBUG, "Continuing with {}".format(current_auth))
                            self.transport._send_message(continue_message)
                            continue
                    except AuthenticationException as e:
                        self._log(DEBUG, "Unable to continue {}: {!r}".format(current_auth, e))
                # Pick another (compatible) AuthMethod
                for method in self.ssh_config["preferredauthentications"].split(","):
                    if (method in self.available_methods and
                        method in server_accepts):
                        try:
                            current_auth = next(self.available_methods[method])
                            self._log(DEBUG, "Next authentication method: {}".format(current_auth))
                            self.transport._send_message(current_auth.message())
                            break
                        except StopIteration:
                            self._log(DEBUG, "No more {} attempts available".format(method))
                else:
                    self._log(INFO, "Client has run out of authentication methods")
                    raise AuthenticationException("Client has run out of authentication methods")
        except Exception as e:
            self._log(ERROR, "Exception in authenticate(): {!r}".format(e))
            exc_type, exc_value, exc_traceback = sys.exc_info()
            self._log(DEBUG, traceback.format_exc())
        finally:
            self.transport.lock.release()
        return self.authenticated

    def sources_from_kwargs(self, kwargs):
        # TODO: **kwargs? whatever, this is mostly internal
        # TODO: this should implement, and document, the current (and/or then
        # desired) way that a pile of kwargs becomes an ordered set of
        # attempted auths...
        pass


class AuthMethod(object):
    """
    Class for ssh (client) user authentication. Implements the "auth_none"
    method, but can be used as a base class for other authentication types.
    """
    method_name = "auth_none"

    def __init__(self, authenticator, *args):
        self.authenticator = authenticator
        self.additional_args(*args)

    # Should override
    def additional_args(self, *args):
        if args:
            raise AuthenticationException("{}: no additional args supported".format(self.method_name))

    def message(self, *args):
        m = Message()
        m.add_byte(cMSG_USERAUTH_REQUEST)
        m.add_string(self.authenticator.username)
        m.add_string('ssh-connection')
        m.add_string(self.method_name)
        self._append_message(m)
        return m

    # Should override
    def _append_message(self, m):
        # No additional message fields for auth_none
        return

    # Should override
    def additional_info(self, ptype, m):
        # Continue dialog with server - varies based on authentication type
        # Should return a Message object if able to respond intelligently,
        # otherwise None to indicate that this current auth type should
        # be cleanly aborted in favor of the next available method attempt.
        raise AuthenticationException("Unexpected continuation message for {}: {:d}".format(self.method_name, ptype))

    @classmethod
    def factory(cls, authenticator, *args, **kwargs):
        # Generate Auth objects per each qualifying arg, if applicable
        # If method is single-user (auth_none, auth_gssapi_keyex), then
        # ignore args, and yield just the single AuthMethod object.
        yield cls(authenticator)

    def __str__(self):
        return self.method_name

AuthNone = AuthMethod


class AuthPassword(AuthMethod):
    method_name = "password"

    def additional_args(self, password):
        if password is not None:
            self.password = password
            return
        # Interactive password prompt
        self.password = getpass.getpass("{}@{}'s password: ".format(
            self.authenticator.username, self.authenticator.transport.hostname))

    def _append_message(self, m):
        m.add_boolean(False)
        m.add_string(self.password)

    def additional_info(self, ptype, m):
        # RFC4252 documents SSH_MSG_USERAUTH_PASSWD_CHANGEREQ as a possibiilty
        # although OpenSSH seems to only perform this during keyboard-interactive
        # but use this as a stub just in case...
        if ptype != MSG_USERAUTH_PASSWD_CHANGEREQ:
            raise AuthenticationException("Unexpected continuation message for {}: {:d}".format(self.method_name, ptype))
        raise AuthenticationException("Server requires password to be changed")

    @classmethod
    def factory(cls, authenticator, *args):
        for pw in args:
            yield cls(authenticator, pw)
        # After trying listed passwords, can include interactive
        # password prompts after exhausting the password list
        if authenticator.ssh_config["batchmode"] == "no":
            for x in range(int(authenticator.ssh_config["numberofpasswordprompts"])):
                yield cls(authenticator, None)

    def __str__(self):
        hash = hashlib.sha1(self.password.encode())
        return "Password:SHA1({})".format(hash.hexdigest())


class AuthKeyboardInteractive(AuthMethod):
    method_name = "keyboard-interactive"

    def additional_args(self, *args):
        # args can be a sequence of (regex, string) pairs to be used
        # as a reply-bot, before (possibly) falling back to actually
        # doing an interactive prompt with keyboard input.
        self.auto_replies = args

    def _append_message(self, m):
        m.add_string("") # Language tag (deprecated)
        m.add_string(self.authenticator.ssh_config["kbdinteractivedevices"])

    def additional_info(self, ptype, m):
        # RFC4252 documents SSH_MSG_USERAUTH_PASSWD_CHANGEREQ as a possibiilty
        # although OpenSSH seems to only perform this during keyboard-interactive
        # but use this as a stub just in case...
        if ptype != MSG_USERAUTH_INFO_REQUEST:
            raise AuthenticationException("Unexpected continuation message for {}: {:d}".format(self.method_name, ptype))
        name = m.get_text()
        instruction = m.get_text()
        language_tag = m.get_text()
        n_prompts = m.get_int()
        self.authenticator._log(DEBUG, "KeyboardInteractive session:\nName: {}\nInstruction: {}\nPrompts: {:d}".format(
            name, instruction, n_prompts
        ))
        prompt_list = []
        reply = Message()
        reply.add_byte(cMSG_USERAUTH_INFO_RESPONSE)
        reply.add_int(n_prompts)

        for n in range(n_prompts):
            prompt_text = m.get_text()
            prompt_echo = m.get_boolean()
            for regex, answer in self.auto_replies:
                if re.search(regex, prompt_text):
                    reply.add_string(answer)
                    if prompt_echo:
                        self.authenticator._log(DEBUG, "Auto-fill {} ({})".format(prompt_text, answer))
                    else:
                        self.authenticator._log(DEBUG, "Auto-fill {} ({})".format(prompt_text, "*" * len(answer)))
                    break
            else:
                if self.authenticator.ssh_config["batchmode"] == "no":
                    reply.add_string(getpass.getpass(prompt_text))
                else:
                    self.authenticator._log(DEBUG, "No auto-reply available for prompt ({}) - auto-fill with empty string".format(prompt_text))
                    reply.add_string("")
        return reply

    @classmethod
    def factory(cls, authenticator, *args):
        if args:
            # Setup as auto-reply bot
            yield cls(authenticator, *args)
        # After trying listed passwords, can include interactive
        # password prompts (3)
        if authenticator.ssh_config["batchmode"] == "no":
            for x in range(int(authenticator.ssh_config["numberofpasswordprompts"])):
                yield cls(authenticator)

    def __str__(self):
        if self.auto_replies:
            return "KeyboardInteractive with auto-reply for ({})".format(",".join([regex for regex, answer in self.auto_replies]))
        else:
            return "KeyboardInteractive"


class AuthPublicKey(AuthMethod):
    method_name = "publickey"

    def additional_args(self, pkey):
        # Accept PKey type (not filename)
        self.pkey = pkey
        self.sign_data = False

    def _append_message(self, m):
        m.add_boolean(self.sign_data)
        if self.pkey.public_blob:
            m.add_string(self.pkey.public_blob.key_type)
            m.add_string(self.pkey.public_blob.key_blob)
        else:
            m.add_string(self.pkey.get_name())
            m.add_string(self.pkey.asbytes())
        if self.sign_data:
            blob = self._get_session_blob(
                self.pkey, 'ssh-connection', self.authenticator.username)
            sig = self.pkey.sign_ssh_data(blob)
            m.add_string(sig)

    def _get_session_blob(self, key, service, username):
        m = Message()
        m.add_string(self.authenticator.transport.session_id)
        m.add_byte(cMSG_USERAUTH_REQUEST)
        m.add_string(username)
        m.add_string(service)
        m.add_string('publickey')
        m.add_boolean(True)
        # Use certificate contents, if available, plain pubkey otherwise
        if key.public_blob:
            m.add_string(key.public_blob.key_type)
            m.add_string(key.public_blob.key_blob)
        else:
            m.add_string(key.get_name())
            m.add_string(key)
        return m.asbytes()

    @classmethod
    def factory(cls, authenticator, *args):
        # Keep track of attempted keys/certs by fingerprint, since
        # agent and identities may overlap with the provided list.
        attempted = []
        keys = list(args)
        # Add Agent keys and Identities if requested
        if authenticator.ssh_config["identitiesonly"] == "no":
            agent = Agent()
            keys.extend(agent.get_keys())
            for keytype in ("rsa", "rsa", "ed25519", "ecdsa", "dss", "rsa"):
                keys.append("~/.ssh/id_{}-cert.pub".format(keytype))
                keys.append("~/ssh/id_{}-cert.pub".format(keytype))
                keys.append("~/.ssh/id_{}".format(keytype))
                keys.append("~/ssh/id_{}".format(keytype))

        for key in keys:
            if not isinstance(key, PKey):
                # Filename... Try various types
                filename = os.path.expanduser(key)
                if filename.endswith("-cert.pub"):
                    private_file = filename[:-9]
                elif filename.endswith(".pub"):
                    private_file = filename[:-4]
                else:
                    private_file = filename
                try:
                    fileobj = StringIO(open(private_file, "r").read())
                except IOError as e:
                    # authenticator._log(DEBUG, "Unable to open {}: {}".format(private_file, e))
                    continue
                for pkey_class in (RSAKey, ECDSAKey, Ed25519Key, DSSKey):
                    try:
                        fileobj.seek(0, os.SEEK_SET)
                        pkey = pkey_class.from_private_key(fileobj, authenticator.passphrase)
                        if filename.endswith("-cert.pub"):
                            pkey.load_certificate(filename)
                        break
                    except Exception as e:
                        # authenticator._log(DEBUG, "Failed to load {} as {} - {}".format(private_file, pkey_class, e))
                        pass
                else:
                    authenticator._log(DEBUG, "Unable to load key from {}".format(key))
                    continue
                key = pkey

            if key.public_blob:
                keytype = key.public_blob.key_type
            else:
                keytype = key.get_name()

            if (keytype, key.get_fingerprint()) not in attempted:
                attempted.append((keytype, key.get_fingerprint()))
                yield cls(authenticator, key)
            else:
                authenticator._log(DEBUG, "Skipping {} - {} (was previously attempted)".format(keytype,
                    binascii.hexlify(key.get_fingerprint())))

    def additional_info(self, ptype, m):
        # Original Auth message did not include signed data, and the server
        # indicates that this key is acceptable, contingent on proving we
        # do have the private key to crypto-sign the message contents.
        if ptype != MSG_USERAUTH_PK_OK:
            raise AuthenticationException("Unexpected continuation message for {}: {:d}".format(self.method_name, ptype))
        # If support for deferring the private key passphrase application
        # gets implemented, here would be a great place to use it...
        self.sign_data = True
        return self.message()

    def __str__(self):
        if self.pkey.public_blob:
            keyname = self.pkey.public_blob.key_type
        else:
            keyname = self.pkey.get_name()
        return "{} - {}".format(keyname, binascii.hexlify(self.pkey.get_fingerprint()))
            #  ':'.join(["{:02x}".format(ord(x)) for x in self.pkey.get_fingerprint()]))

class AuthGSSAPI(AuthMethod):
    # RFC4462 - GSSAPI Authentication
    method_name = "gssapi-with-mic"

    def additional_args(self, *args):
        self.sshgss = GSSAuth(self.method_name, self.authenticator.ssh_config.get("gssapidelegatecredentials") == "yes")
        self.mech = None

    def _append_message(self, m):
        m.add_bytes(self.sshgss.ssh_gss_oids())

    @classmethod
    def factory(cls, authenticator, *args):
        # Support only for Kerberos based GSS method, so only one OID
        try:
            yield cls(authenticator)
        except Exception as e:
            authenticator._log(INFO, "GSSAPI failure - {}".format(str(e)))

    def __str__(self):
        return "GSSAPI (with MIC) using Kerberos"

    def additional_info(self, ptype, m):
        if ptype ==  MSG_USERAUTH_GSSAPI_RESPONSE:
            # Server passed the selected mechanism (OID)
            self.mech = m.get_string()
            self.authenticator._log(DEBUG, "Server mechanism: {}".format(binascii.hexlify(self.mech)))
            ctx = self.sshgss.ssh_init_sec_context(
                self.authenticator.transport.hostname, # self.gss_host,
                self.mech,
                self.authenticator.username)
            m = Message()
            m.add_byte(cMSG_USERAUTH_GSSAPI_TOKEN)
            m.add_string(ctx)
            self.authenticator._log(DEBUG, "GSSAPI Token generated from ssh_init_sec_context(): {}".format(binascii.hexlify(ctx)))
            return m
        if ptype == MSG_USERAUTH_GSSAPI_TOKEN:
            # Reprocess context with supplied token from server
            srv_token = m.get_string()
            self.authenticator._log(DEBUG, "Server reply with GSSAPI Token: {}".format(binascii.hexlify(srv_token)))
            next_token = self.sshgss.ssh_init_sec_context(
                "", # self.gss_host,
                self.mech,
                self.authenticator.username,
                srv_token)
            if next_token:
                m = Message()
                m.add_byte(cMSG_USERAUTH_GSSAPI_TOKEN)
                m.add_string(next_token)
                self.authenticator._log(DEBUG, "Client answer with GSSAPI Token: {}".format(binascii.hexlify(next_token)))
                return m
            m = Message()
            m.add_byte(cMSG_USERAUTH_GSSAPI_MIC)
            mic = self.sshgss.ssh_get_mic(self.authenticator.transport.session_id)
            m.add_string(mic)
            self.authenticator._log(DEBUG, "Client finishing with GSSAPI MIC: {}".format(binascii.hexlify(mic)))
            return m
        raise AuthenticationException("Unexpected message type for {}: {:d}".format(self.method_name, ptype))
