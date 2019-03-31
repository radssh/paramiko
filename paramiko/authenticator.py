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
import logging
import itertools

try:
    import Queue
    from StringIO import StringIO
except ImportError:
    import queue as Queue
    from io import StringIO

import six

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

# Should rest of Paramiko replace AuthHandler usage with Authenticator
replace_auth_handler = True

# Helper function to get identity filenames from ~/.ssh or ~/ssh (Windows)
# Will also find certificate files as well as private key files
def default_identity_files():
    for sshdir in (os.path.expanduser("~/.ssh"), os.path.expanduser("~/ssh")):
        if os.path.isdir(os.path.expanduser(sshdir)):
            for keytype in ("rsa", "ed25519", "ecdsa", "dsa"):
                keyfile = os.path.join(sshdir, "id_{}".format(keytype))
                certfile = os.path.join(sshdir, "id_{}-cert.pub".format(keytype))
                if os.path.exists(keyfile):
                    yield keyfile
                if os.path.exists(certfile):
                    yield certfile


class Authenticator(object):
    """
    Wraps a `Transport` and uses it to authenticate or die trying.

    Lifecycle is relatively straightforward:

    - Instantiate with a `Transport` handle, along with an optional collection
      of core parameters. Many of the previous options have been moved from
      core options into a generic ssh_config style of option tracking that
      can be customized with one (or more) subsequent calls to
      `update_authentication_options()`.
      The core options are:
        - username (can be updated with ssh_config `User`)
        - default_password (for password authentication)
        - key_or_keyfile (`PKey` or filename)
        - passphrase (distinct from default_password, for decrypting keyfile)

    - If desired, tweak the default ssh_config options setup in the
      Authenticator, using `update_authentication_options()`. In most cases,
      this will not be strictly necessary, unless the OpenSSH client would
      need additional options specified (typically in ~/.ssh/config or with
      command line switches "-o keyword=value"). These options will use
      the OpenSSH setting names and values, and may be specified via a dict
      (returned from SSHConfig.lookup), or by keyword arguments:
      `update_authentication_options(BatchMode="no",
                                     NumberOfPasswordPrompts="1")`
      Note: Only option names pertaining to user authentication are in scope

    - Call the instance's `authenticate` method, which will make use of
      one or more available authentication methods managed by the Authenticator
      object itself. The authenticate() call will:
        - attempt to authenticate in a server-driven order of preference
        - if successful, return `True`
        - if unsuccessful or if additional auth factors are required, return
          `False` (typically) or raise an `AuthenticationException` (or
          subclass thereof) which will convey details of complications
          encountered. The distinction is that False should be returned in
          situations where the client/server communication is behaving fine,
          but the server declines the various authentication attempts being
          offered. `AuthenticationException` should be raised only if there
          was a more unusual event occurring during processing.
        - either way, the point is that the caller will have authenticated
          successfully, or have an unauthenticated `Transport` to continue
          authentication attempts via other method(s).
        - see API docs for `authenticate` for further details.

    - Alternately, for tighter control of which auth sources are tried and in
      what order, call `auth_$method` components directly, following the model
      of the legacy `AuthHandler`, for true backward compatibility.
    """
    service_name = "ssh-userauth"

    # Default settings for authentication options, in the style of
    # OpenSSH config. Can be updated from dict options from SSHConfig.lookup()
    # or from a manually constructed dict.
    # Differences from OpenSSH defaults:
    # - BatchMode defaults to 'yes' instead of 'no'
    # - User and Hostname are initially left unset
    default_ssh_config = {
        "gssapiauthentication": "no",
        "hostbasedauthentication": "no",
        "pubkeyauthentication": "yes",
        "kbdinteractiveauthentication": "yes",
        "passwordauthentication": "yes",
        "challengeresponseauthentication": "yes",
        "preferredauthentications": "gssapi-with-mic,hostbased,publickey,keyboard-interactive,password",
        "batchmode": "yes",
        "enablesshkeysign": "no",
        "fingerprinthash": "sha256",
        "gssapidelegatecredentials": "no",
        "gssapi-keyex": "yes",
        "identitiesonly": "no",
        "identityagent": "SSH_AUTH_SOCK",
        "kbdinteractivedevices": "",
        "numberofpasswordprompts": "3",
        # These could have defaults now, but leave them None for now
        "user": None, # Filled in later
        "hostname": None, # Needed for GSSAPI

        # Placeholders/Reminders for future support

        # TBD: CertificateFile processing in OpenSSH is contingent on pariing
        # with a corresponding IdentityFile in scope with the same pubkey,
        # not based on filename. Paramiko's current handling of certificates
        # has a rather close dependency on filenames, so for now we just
        # permit usage of certificate filenames as IdentityFile to imply
        # a "Load both of these things"
        "identityfile": None, # Actually a list, but avoid populating default with a mutable type
        # "certificatefile": [],

        # Add this option when the AuthHostBased class is implemented
        # "hostbasedkeytypes": "",

        # Future enhancement - support this for better smartcard support
        # "pkcs11provider": "", # TBD

        # Future enhancement
        # "pubkeyacceptedkeytypes": "",
    }

    def __init__(self,
            transport,
            username=None,
            default_password=None,
            keyfile_or_key=None,
            passphrase=None,
            ):
        # TODO: consider adding some more of SSHClient.connect (optionally, if
        # the caller didn't already do these things) like the call to
        # .start_client; then update lifecycle in docstring.

        self.transport = transport
        self.ssh_config = dict(self.default_ssh_config)
        self._log = logging.getLogger("paramiko.authenticator").log
        if username:
            self.ssh_config["user"] = username
        if default_password is not None:
            self.password_list = [default_password]
        else:
            self.password_list = []
        self.default_password = default_password
        if keyfile_or_key:
            self.key_list = [keyfile_or_key]
        else:
            self.key_list = []
        self.passphrase = passphrase
        self.interactive_replybots = []
        self.interactive_handlers = []
        # State of authentication
        self.server_reply = Queue.Queue()
        self.authenticated = False
        self.in_progress = False
        self.server_accepts = [] # Pending initial auth_none
        self.authenticated_sequence = []
        self.banner = None
        # Temporary, for backward compatibility with legacy AuthHandler
        def makeshift_handler(ptype):
            def fn(self, m):
                self.server_reply.put((ptype, m))
            return fn
        self._handler_table = {}
        for ptype in range(MSG_USERAUTH_REQUEST, 79): # HIGHEST_USERAUTH_MESSAGE_ID
            self._handler_table[ptype] = makeshift_handler(ptype)
        self._handler_table[MSG_SERVICE_ACCEPT] = makeshift_handler(MSG_SERVICE_ACCEPT)

    def update_authentication_options(self, config_dict=None, **kwargs):
        """
        SSHConfig.lookup() or manually constructed dict
        Lists will be extended with updated values
        Values starting with + or - will append or subtract from a
        comma-separated string
        Other values will be substituted in whole
        """
        if config_dict:
            settings = itertools.chain(config_dict.items(), kwargs.items())
        else:
            settings = kwargs.items()
        for k, v in settings:
            # Normalize keys to lowercase
            k = k.lower()
            if k not in self.ssh_config:
                continue
            if isinstance(v, list):
                if self.ssh_config[k]:
                    self.ssh_config[k].extend(v)
                else:
                    self.ssh_config[k] = list(v)
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

    def is_authenticated(self):
        return self.authenticated

    def abort(self):
        # Something bad happened at the transport layer
        if self.in_progress:
            # Fabricate a failure message with a bogus list of methods that may
            # continue, so we don't block on reading response that might not
            # get delivered, due to disconnect.
            m = Message()
            m.add_string("aborted")
            m.add_boolean(False)
            m.rewind()
            self.server_reply.put((MSG_USERAUTH_FAILURE, m))
            self.in_progress = False

    def add_replybot(self, *replies):
        # Pre-canned responses for automated keyboard-interactive processing
        # Alternative to setting up a callback handler, uses a list of
        # (regex, answer) pairs.
        self.interactive_replybots.append(replies)

    def add_handler(self, handler):
        self.interactive_handlers.append(handler)

    def authenticate(self, explicit_methods=None, force_service_request=False):
        # TODO: define AuthSource (maybe rename...lol), should be lightweight,
        # pairing an auth type with some value or iterable of values
        # TODO: implement cleaner version of SSHClient._auth, somehow, that
        # handles multi-factor auth much better than the current shite
        # trickledown. (Be very TDD here...! Perhaps wait until single-source
        # tests all pass first, then can ensure they continue to do so?)
        if not self.transport.active or not self.transport.initial_kex_done:
            raise AuthenticationException("No existing session")
        if self.authenticated:
            raise AuthenticationException("Transport already authenticated")

        # Set the username from ssh_config, if not already set at __init__()
        # or updated via `update_authentication_options()`
        if self.ssh_config["user"] is None:
             self.ssh_config["user"] = getpass.getuser()
        if explicit_methods is not None:
            # User supplied dict of method/iterators to use
            preferred_authentications = list(explicit_methods)
            self.available_methods = explicit_methods
        else:
            # Assemble a MFA-capable dict of method names with iterators
            # for various AuthMethod objects to attempt, according to
            # what the server passes back in the MSG_USERAUTH_FAILURE content.
            preferred_authentications = self.ssh_config["preferredauthentications"].split(",")
            self.available_methods = {}
            if self.ssh_config["passwordauthentication"] == "yes":
                self.available_methods["password"] = AuthPassword.factory(self, *self.password_list)
            if self.ssh_config["pubkeyauthentication"] == "yes":
                self.available_methods["publickey"] = AuthPublicKey.factory(self, *self.key_list)
            if self.ssh_config["kbdinteractiveauthentication"] == "yes":
                if not self.interactive_handlers and not self.interactive_replybots:
                    # Fallback option to supply password during keyboard-interactive
                    if len(self.password_list) == 1:
                        self.add_replybot(('.', self.password_list[0]))
                self.available_methods["keyboard-interactive"] = AuthKeyboardInteractive.factory(self, handlers=self.interactive_handlers, reply_bots=self.interactive_replybots)
            if self.ssh_config["gssapiauthentication"] == "yes":
                self.available_methods["gssapi-with-mic"] = AuthGSSAPI.factory(self)
                if self.ssh_config["gssapi-keyex"] == "yes":
                    # gssapi-keyex preferred priority
                    preferred_authentications.insert(0, "gssapi-keyex")
                    self.available_methods["gssapi-keyex"] = AuthGSSAPI_Keyex.factory(self)
        # Use ssh_config IdentityAgent setting (replaces allow_agent)
        ssh_agent = self.ssh_config.get("identityagent", "SSH_AUTH_SOCK")
        if ssh_agent == "none" and "SSH_AUTH_SOCK" in os.environ:
            os.environ.pop("SSH_AUTH_SOCK")
            self._log(DEBUG, "Disabling ssh-agent key lookups (IdentityAgent none)")
        elif ssh_agent != "SSH_AUTH_SOCK":
            os.environ["SSH_AUTH_SOCK"] = ssh_agent
            self._log(DEBUG, "Redirecting ssh-agent key lookups (IdentityAgent {})".format(ssh_agent))


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
                resp = self.server_reply.get(timeout=self.transport.auth_timeout)
                ptype, m = resp
                if ptype != MSG_SERVICE_ACCEPT:
                    raise AuthenticationException("Expected cMSG_SERVICE_ACCEPT(6), but got {:d}".format(ptype))
                service_name = m.get_text()
                if service_name !=  self.service_name:
                    raise AuthenticationException("Unexpected service name: expected {}, got {}".format(self.service_name, service_name))
                self._log(DEBUG, "Server accepted {} request".format(self.service_name))
                self.in_progress = True

            # Issue an auth_none before the loop, regardless of if this is
            # intial call, or a followup to authenticate
            current_auth = AuthNone(self)
            self.transport._send_message(current_auth.message())

            while self.in_progress:
                try:
                    ptype, m = self.server_reply.get(timeout=self.transport.auth_timeout)
                except Queue.Empty:
                    raise AuthenticationException("Server reply timeout during authentication")
                self._log(DEBUG, "Got reply from server: {:d}".format(ptype))

                if ptype == MSG_USERAUTH_SUCCESS:
                    self._log(INFO, "Authentication success!")
                    self.authenticated = True
                    self.in_progress = False
                    self.authenticated_sequence.append(current_auth)
                    self.transport._auth_trigger()
                    break
                elif ptype == MSG_USERAUTH_BANNER:
                    banner = m.get_text()
                    language = m.get_text()
                    self._log(DEBUG, "Banner received: {} ({})".format(banner.strip(), language))
                    self.banner = banner
                    continue
                elif ptype == MSG_USERAUTH_FAILURE:
                    self.server_accepts = m.get_text().split(',')
                    partial_success = m.get_boolean()
                    if partial_success:
                        self._log(INFO, "Authentication {} partial success".format(current_auth))
                        self.authenticated_sequence.append(current_auth)
                    else:
                        self._log(INFO, "Authentication {} failed".format(current_auth))
                    self._log(DEBUG, "Authentications that can continue: {}".format(",".join(self.server_accepts)))
                    self._log(DEBUG, "Client preferred authentications: {}".format(preferred_authentications))
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
                for method in preferred_authentications:
                    if (method in self.available_methods and
                        method in self.server_accepts):
                        try:
                            current_auth = next(self.available_methods[method])
                            self._log(DEBUG, "Next authentication method: {}".format(current_auth))
                            self.transport._send_message(current_auth.message())
                            break
                        except StopIteration:
                            self._log(DEBUG, "No more {} attempts available".format(method))
                else:
                    self._log(INFO, "Client has run out of authentication methods")
                    # raise AuthenticationException("Client has run out of authentication methods")
                    return False
        except Exception as e:
            # Catch-all, but relabel this as AuthenticationException
            # preserving the traceback
            self._log(ERROR, "Exception in authenticate(): {!r}".format(e))
            exc_type, exc_value, exc_traceback = sys.exc_info()
            six.raise_from(AuthenticationException, e)

        finally:
            self.transport.lock.release()
        return self.authenticated

    # Legacy interface calls - for backward compatibility only
    def auth_none(self, username, event):
        self._log(INFO, "Deprecated Transport.auth_none() called - switch to Authenticator")
        if username != self.ssh_config["user"]:
            raise AuthenticationException("Change of user not permitted")
        self.authenticate({})
        if event:
            event.set()

    def auth_gssapi_keyex(self, username, event):
        self._log(INFO, "Deprecated Transport.auth_gssapi_keyex() called - switch to Authenticator")
        if username != self.ssh_config["user"]:
            raise AuthenticationException("Change of user not permitted")
        self.authenticate({"gssapi-keyex": AuthGSSAPI_Keyex.factory(self)})
        if event:
            event.set()

    def auth_gssapi_with_mic(self, username, gss_host, gss_deleg_creds, event):
        self._log(INFO, "Deprecated Transport.auth_gssapi_with_mic() called - switch to Authenticator")
        if username != self.ssh_config["user"]:
            raise AuthenticationException("Change of user not permitted")
        self.update_authentication_options(
            Hostname=gss_host,
            GSSAPIDelegateCredentials="yes" if gss_deleg_creds else "no"
        )
        self.authenticate({"gssapi-with-mic": AuthGSSAPI.factory(self)})
        if event:
            event.set()

    def auth_password(self, username, password, event):
        self._log(INFO, "Deprecated Transport.auth_password() called - switch to Authenticator")
        if username != self.ssh_config["user"]:
            raise AuthenticationException("Change of user not permitted")
        self.authenticate({"password": AuthPassword.factory(self, password)})
        if event:
            event.set()


    def auth_interactive(self, username, handler, event, submethods=''):
        self._log(INFO, "Deprecated Transport.auth_interactive() called - switch to Authenticator")
        if username != self.ssh_config["user"]:
            raise AuthenticationException("Change of user not permitted")
        if submethods:
            self.update_authentication_options(KbdInteractiveDevices=submethods)
        if handler:
            self.authenticate({"keyboard-interactive": AuthKeyboardInteractive.factory(self, handlers=[handler])})
        else:
            self.authenticate({"keyboard-interactive": AuthKeyboardInteractive.factory(self)})
        if event:
            event.set()


    def auth_publickey(self, username, key, event):
        self._log(INFO, "Deprecated Transport.auth_publickey() called - switch to Authenticator")
        if username != self.ssh_config["user"]:
            raise AuthenticationException("Change of user not permitted")
        # Safe change of SSH options IdentityFile & IdentitiesOnly
        save_config = self.ssh_config
        # ensure dict keys in lowercase, since it's being built manually
        self.ssh_config = dict(
            user = save_config.get('user', getpass.getuser()),
            identitiesonly = "yes",
            identityfile = [key]
        )
        self.authenticate({"publickey": AuthPublicKey.factory(self)})
        self.ssh_config = save_config
        if event:
            event.set()

    def wait_for_response(self, event):
        # No longer support asynchronous authentication, and we can
        # better rely on AuthenticationException being thrown without
        # bending over backward to save it. So the return options
        # become the list of allowed authentication types (if not authenticated)
        # or an empty list if authentication was successful.
        self._log(INFO, "Deprecated AuthHandler.wait_for_response() called - switch to Authenticator")
        if not self.is_authenticated():
            return self.server_accepts
        return []


class AuthMethod(object):
    """
    Base class for ssh (client) user authentication. Implements the "auth_none"
    method, but can be used as a base class for other authentication types.
    """
    method_name = "AuthMethodBase"

    # Must override
    def __init__(self, authenticator):
        self.authenticator = authenticator
        # Base class only - do not use directly
        if self.method_name == "AuthMethodBase":
            raise AuthenticationException("AuthMethod should not be used directly - use one of (AuthPassword, AuthPublicKey, etc.) instead")

    def message(self, *args):
        # Build the start of a USERAUTH_REQUEST message, then pass it to
        # the derived class _append_message() to complete. This is the
        # initial request starting a new authentication method attempt.
        m = Message()
        m.add_byte(cMSG_USERAUTH_REQUEST)
        m.add_string(self.authenticator.ssh_config["user"])
        m.add_string('ssh-connection')
        m.add_string(self.method_name)
        self._append_message(m)
        return m

    # Must override
    def _append_message(self, m):
        raise AutheticationException("AuthMethod._append_message() should not be used directly")

    # Should override, if any SSH AdditionalInfo messages are defined
    # for this AuthMethod
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

class AuthNone(AuthMethod):
    # Borderline trivial build on top of base class, as there are no
    # additional fields to populate in the request message, and no
    # defined followup responses. auth_none is not expected to succeed
    # (although it might), but can be useful to safely get the server
    # to respond with the list of allowed authentication methods.
    method_name = "auth_none"

    def __init__(self, authenticator):
        AuthMethod.__init__(self, authenticator)

    def _append_message(self, m):
        return

class AuthPassword(AuthMethod):
    method_name = "password"

    def __init__(self, authenticator, password):
        AuthMethod.__init__(self, authenticator)
        if password is not None:
            self.password = password
            return
        # Interactive password prompt
        self.password = getpass.getpass("{}@{}'s password: ".format(
            self.authenticator.ssh_config["user"],
            self.authenticator.ssh_config["hostname"]))

    def _append_message(self, m):
        m.add_boolean(False)
        m.add_string(self.password)

    def additional_info(self, ptype, m):
        # RFC4252 documents SSH_MSG_USERAUTH_PASSWD_CHANGEREQ as a possibiilty
        # although OpenSSH seems to only perform this during keyboard-interactive
        # but use this as a stub just in case...
        # https://marc.info/?l=openssh-unix-dev&m=153831284026324&w=2
        if ptype != MSG_USERAUTH_PASSWD_CHANGEREQ:
            raise AuthenticationException("Unexpected continuation message for {}: {:d}".format(self.method_name, ptype))
        raise AuthenticationException("Server requires password to be changed")

    @classmethod
    def factory(cls, authenticator, *args):
        # Zero or more pre-filled passwords
        for pw in args:
            yield cls(authenticator, pw)
        # After trying listed passwords, can include interactive
        # password prompts after exhausting the password list
        if authenticator.ssh_config["batchmode"] == "no":
            for x in range(int(authenticator.ssh_config["numberofpasswordprompts"])):
                yield cls(authenticator, None)

    def __str__(self):
        # Having the hash value handy for debug, but potentailly bad security
        # hash = hashlib.sha1(self.password.encode())
        # return "Password:SHA1({})".format(self.password)
        return "Password"

class AuthKeyboardInteractive(AuthMethod):
    method_name = "keyboard-interactive"

    def __init__(self, authenticator, handler=None, auto_replies=None):
        AuthMethod.__init__(self, authenticator)
        # Support old-style handler (callable), or a list/tuple
        # of auto_reply pairs (regex, reply_text)
        self.auto_replies = auto_replies or []
        self.handler = handler

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
        for p in range(n_prompts):
            prompt_list.append((m.get_text(), m.get_boolean()))

        reply = Message()
        reply.add_byte(cMSG_USERAUTH_INFO_RESPONSE)
        reply.add_int(n_prompts)
        if self.handler:
            # Pass the whole prompt data to the supplied handler callable
            self.authenticator._log(DEBUG, "Calling supplied prompt handler")
            for answer in self.handler(name, instructions, prompt_list):
                reply.add_string(answer)
        else:
            for prompt_text, prompt_echo in prompt_list:
                for regex, answer in self.auto_replies:
                    if re.search(regex, prompt_text):
                        if prompt_echo:
                            self.authenticator._log(DEBUG, "Auto-fill {} ({})".format(prompt_text, answer))
                        else:
                            self.authenticator._log(DEBUG, "Auto-fill {} ({})".format(prompt_text, "*" * len(answer)))
                        reply.add_string(answer)
                        break
                else:
                    if self.authenticator.ssh_config["batchmode"] == "no":
                        reply.add_string(getpass.getpass(prompt_text))
                    else:
                        self.authenticator._log(DEBUG, "No auto-reply available for prompt ({}) - auto-fill with empty string".format(prompt_text))
                        reply.add_string("")
        return reply

    @classmethod
    def factory(cls, authenticator, handlers=None, reply_bots=None):
        if handlers:
            for h in handlers:
                yield cls(authenticator, handler=h)
        if reply_bots:
            for bot in reply_bots:
                yield cls(authenticator, auto_replies=bot)
        # After trying supplied handlers/responders, can include interactive
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

    def __init__(self, authenticator, pkey):
        AuthMethod.__init__(self, authenticator)
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
                self.pkey, 'ssh-connection', self.authenticator.ssh_config["user"])
            sig = self.pkey.sign_ssh_data(blob)
            m.add_string(sig)

    def _get_session_blob(self, key, service, username):
        # This constructed message is not actually passed, but instead
        # built on the client side for signing, then the server side
        # independently constructs this same message content in order
        # to validate the signature
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
        if authenticator.ssh_config.get("identityfile"):
            identity_files = authenticator.ssh_config.get("identityfile")
        else:
            # Prepare the list of default identity files
            identity_files = default_identity_files()
        # IdentitiesOnly controls the usage of ssh-agent to find additional keys
        if authenticator.ssh_config["identitiesonly"] == "no":
            agent = Agent()
            keys.extend(agent.get_keys())
        # Mimic the old look_for_keys by interpreting IdentitiesOnly based
        # on whether there was an explicit list of keys passed in, which
        # overrides IdentityFile configuration settings.
        if authenticator.ssh_config.get("identitiesonly") == "no" or not args:
            authenticator._log(DEBUG, "Adding identity files: {}".format(identity_files))
            keys.extend(identity_files)
        authenticator._log(DEBUG, "Available PKeys: {}".format(keys))

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
    # Client offers a list of OIDs (currently only support KRB5)
    # If the server accepts, then the client comutes a token using
    # `ssh_init_sec_context()` and responds to the server with that
    # token. The server may continue offering updated tokens until the
    # client arrives at an empty token, at which point it passes back
    # the derived Message Integrity Code (MIC) for the session.
    method_name = "gssapi-with-mic"

    def __init__(self, authenticator, *args):
        AuthMethod.__init__(self, authenticator)
        self.sshgss = GSSAuth(
            self.method_name,
            self.authenticator.ssh_config.get("gssapidelegatecredentials") == "yes"
        )
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
        return "GSSAPI (with MIC) using Kerberos: {}".format(self.sshgss)

    def additional_info(self, ptype, m):
        if ptype == MSG_USERAUTH_GSSAPI_ERRTOK:
            # Log the error, and move on...
            error_token = m.get_text()
            self.authenticator._log(ERROR, "GSSAPI Error Token received: {}".format(error_token))
            # Server should follow with MSG_USERAUTH_FAILURE, so don't reply with a message here
            return None
        if ptype == MSG_USERAUTH_GSSAPI_ERROR:
            maj_status = m.get_int()
            min_status = m.get_int()
            err_msg = m.get_string()
            self.authenticator._log(ERROR, "GSSAPI Error: {:d}/{:d} {}".format(maj_status, min_status, err_msg))
            # Server should follow with MSG_USERAUTH_FAILURE, so don't reply with a message here
            return None
        if ptype ==  MSG_USERAUTH_GSSAPI_RESPONSE:
            # Server passed the selected mechanism (OID)
            self.mech = m.get_string()
            self.authenticator._log(DEBUG, "Server mechanism: {}".format(binascii.hexlify(self.mech)))
            gss_host = (self.authenticator.ssh_config.get("gssapiserveridentity")
                or self.authenticator.ssh_config["hostname"]
            )
            token = self.sshgss.ssh_init_sec_context(
                gss_host,
                self.mech,
                self.authenticator.ssh_config["user"])
            m = Message()
            m.add_byte(cMSG_USERAUTH_GSSAPI_TOKEN)
            m.add_string(token)
            # Is GSS Token value possibly sensitive information?
            # self.authenticator._log(DEBUG, "GSSAPI Token generated from ssh_init_sec_context(): {}".format(binascii.hexlify(token)))
            return m
        if ptype == MSG_USERAUTH_GSSAPI_TOKEN:
            # Reprocess context with supplied token from server
            srv_token = m.get_string()
            # Is GSS Token value possibly sensitive information?
            # self.authenticator._log(DEBUG, "Server reply with GSSAPI Token: {}".format(binascii.hexlify(srv_token)))
            gss_host = (self.authenticator.ssh_config.get("gssapiserveridentity")
                or self.authenticator.ssh_config["hostname"]
            )
            next_token = self.sshgss.ssh_init_sec_context(
                gss_host,
                self.mech,
                self.authenticator.ssh_config["user"],
                srv_token)
            if next_token:
                m = Message()
                m.add_byte(cMSG_USERAUTH_GSSAPI_TOKEN)
                m.add_string(next_token)
                # Is GSS Token value possibly sensitive information?
                # self.authenticator._log(DEBUG, "Client answer with GSSAPI Token: {}".format(binascii.hexlify(next_token)))
                return m
            m = Message()
            m.add_byte(cMSG_USERAUTH_GSSAPI_MIC)
            mic = self.sshgss.ssh_get_mic(self.authenticator.transport.session_id)
            m.add_string(mic)
            # Is GSS MIC value possibly sensitive information?
            # self.authenticator._log(DEBUG, "Client finishing with GSSAPI MIC: {}".format(binascii.hexlify(mic)))
            return m
        raise AuthenticationException("Unexpected message type for {}: {:d}".format(self.method_name, ptype))


class AuthGSSAPI_Keyex(AuthMethod):
    # RFC4462 - GSSAPI Authentication
    # Simpler mechanism than gssapi-with-mic, but can only be used
    # if the earlier SSH Key Exchange done by `Transport` used GSS
    # for the key exchange. In this case, a GSS context exists that
    # may be permitted, provided the client offers the MIC for that
    # existing context.
    method_name = "gssapi-keyex"

    def __init__(self, authenticator, *args):
        AuthMethod.__init__(self, authenticator)
        if not authenticator.transport.gss_kex_used:
            raise AuthenticationException("gssapi-keyex cannot be used because initial key exchange was not done via GSS")

    def _append_message(self, m):
        kexgss = self.authenticator.transport.kexgss_ctxt
        kexgss.set_username(self.authenticator.ssh_config["user"])
        mic_token = kexgss.ssh_get_mic(self.authenticator.transport.session_id)
        m.add_string(mic_token)

    @classmethod
    def factory(cls, authenticator, *args):
        # Support only for single attempt, per RFC4462
        try:
            yield cls(authenticator)
        except Exception as e:
            authenticator._log(INFO, "GSSAPI-keyex failure - {}".format(str(e)))

    def __str__(self):
        return "GSSAPI (keyex): {}".format(self.authenticator.transport.kexgss_ctxt)
