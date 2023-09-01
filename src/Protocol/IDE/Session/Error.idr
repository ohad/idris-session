||| Protocol errors
module Protocol.IDE.Session.Error

import Network.Socket
import Protocol.SExp.Parser
import Protocol.SExp
import Protocol.IDE

public export
data PropagatedSocketError
  = ||| while reading packet size
    PacketCountSocketError
  | ||| while reading packet payload
    PacketPayloadSocketError
public export
data EncodingError
  = ||| Could not parse packet size
    PacketSizeParse String
  | |||
    PacketMismatch

public export
data SessionSExpError
  = ||| Encoding of protocol is incorrect
    Encoding EncodingError
  | ||| Propagate error from the IDE socket with the context
    ||| in which it happened
    Socket (PropagatedSocketError, SocketError)
  | SExpParse SExpError

public export
data SessionReplyError
  = ||| Propagated error encountered while reading an
    ||| S-expression from the socket and parsing it
    PropagateSExp SessionSExpError
  | ||| Failed to parse the S-expression into a valid IDE Reply
    ParseReply SExp

public export
data ConnectionError
  = ||| Propagated error encountered while reading the greeting
    ||| S-expression from the socket upon initial connection
    ConnectionPropagateSExp SessionSExpError
  | ||| Propagated socket error when trying to create a socket
    ||| fields are the socket configuration attempted
    ||| together with the propagated error
    SocketFailure SocketFamily SocketType ProtocolNumber
                  SocketError
  | ||| Failed to connect the socket to the server
    ConnectionFailure ResultCode
  | ||| Failed the connection handshake due to an unexpected reply
    HandshakeUnexpected Reply
  | ||| Failed the connection handshake due to a parse error
    HandshakeParseError SExp

public export
data SessionError
  = ||| Propagated error encountered while receiving a
    ||| reply to a command
    PropagateReply IDECommand SessionReplyError
  | ||| Received an unexpected reply from the server
    UnexpectedReply IDECommand Reply
  | ||| Encountered socket error while sending a packet
    SendPropagateSocketError IDECommand String SocketError
  | ||| When query the server, we tag it with a unique
    ||| identifier. Thie error means that the reply we got from the
    ||| server doesn't match the query identifier we expect.
    MessageIdentifierMismatch IDECommand Reply Integer
  | ||| Errors happening when trying to connect to the server
    Connection SocketAddress Port ConnectionError
