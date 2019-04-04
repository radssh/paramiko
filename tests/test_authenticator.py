import threading

from paramiko.message import Message
from paramiko.authenticator import Authenticator

from paramiko.common import cMSG_DISCONNECT, cMSG_SERVICE_REQUEST, \
    cMSG_SERVICE_ACCEPT, MSG_SERVICE_ACCEPT

class gss_context(object):
    # GSS tests done elsewhere - this just fabricates some MIC content
    # for gssapi-keyex mockup
    def set_username(username):
        pass
    def ssh_get_mic(session_id):
        return "fake_gss_token"

class AuthOnlyTransport(object):
    """
    Mock Transport class only for Authenticator testing
    Assumes a post-keyexchange connected state, allowing limited
    client requests, with deterministic response mechanisms.
    """
    active = True
    initial_kex_done = True
    lock = threading.Lock()
    auth_timeout = 2

    def __init__(self, users = None, gss_mode=False, session_id='0123456789ABCDEF'):
        """
        users is a dict of allowed users and necessary authentication schemes
        """
        self.users = users
        self.session_id = session_id
        if gss_mode:
            self.gss_kex_used = True
            self.kexgss_ctxt = ""
        else:
            self.gss_kex_used = False
            # kexgss_ctxt unset, should not be referenced
        self.current_user = None
    def _auth_trigger(self):
        pass
    def _send_message(self, m):
        m.rewind()
        ptype = m.get_byte()
        if ptype == cMSG_SERVICE_REQUEST:
            service_name = m.get_text()
            assert service_name == "ssh-userauth"
            callback = self.auth_handler._handler_table[MSG_SERVICE_ACCEPT]
            reply = Message()
            reply.add_string("ssh-userauth")
            reply.rewind()
            callback(self.auth_handler, reply)
            return

        pass

def test_setup01():
    t = AuthOnlyTransport()
    a = Authenticator(t, 'joe')
    t.auth_handler = a
    assert a
    print a.server_reply

    a.authenticate()
