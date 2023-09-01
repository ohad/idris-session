module Protocol.IDE.Session

import Network.Socket
import Network.Socket.Data
import Network.Socket.Raw

import Protocol.Hex
import Protocol.SExp
import Protocol.SExp.Parser

import System

import Protocol.IDE

import Data.DPair
import Data.Either

import Protocol.IDE.Session.Error

{- The server's state machine:

  start
    | RECV: protocol-version        RECV: response1 : r.Response
   v                              v-------+
  READY --- SEND: request r --> PROCESSING r -+
   ^_______________________________|
      RECV :return :ok, :error
-}

public export
data ServerState = Ready | Processing IDECommand | Done

public export
record IDEProtocolVersion where
  constructor MkIDEProtocolVersion
  minor, major : Int

record Server (version : IDEProtocolVersion)
              (state : ServerState) where
  constructor MkServer
  socket : Socket
  msg : Integer

bump : (server : Server version state) ->
  (Integer, Server version state)
bump (MkServer socket msg) = (1+msg, MkServer socket (1+msg))

{-  -- Thanks gallais

%default total

data Command = A | B

namespace Response

  public export
  data Response = C Nat | D | E

Has : Command -> Response -> Type
Has B (C _) = Void
Has _ _ = ()

send : (c : Command) -> ((r : Response) -> (has : Has c r) => a) -> a

hack : (Has c r -> a) -> Has c r => a
hack f = f %search

prog : Nat
prog = send A $ \case
  C v => v
  _ => Z

prog' : Nat
prog' = send B $ \case
  D => Z
  E => hack {c = B, r = E} $ \ prf => ?a
-}

isIntermediate : Reply -> Bool

IsIntermediate, IsImmediate : Reply -> Type
isIntermediate (ProtocolVersion _ _) = False
isIntermediate (Immediate _ _) = False
isIntermediate _ = True

IsIntermediate = So . isIntermediate
IsImmediate = So . not . isIntermediate

decIntermediate : (r : Reply) ->
  Either (IsImmediate r)
         (IsIntermediate r)
decIntermediate r = mirror $ choose (isIntermediate r)


Intermediate : IDECommand -> Reply -> Type
Intermediate _ _ = Void

-- So we need to also implement a validator, as the protocol spec can
-- be wrong!

HasReply : IDECommand -> Reply -> Type
--HasReply (LoadFile _ _) a = ()
--HasReply a b = Void
HasReply a b = Void

hasResult : (c : IDECommand) -> (r : Reply) ->
  Maybe (HasReply c r)
hasResult c r = Nothing

validateReplyFor : (c : IDECommand) -> (r : Reply) ->
  Maybe $ Either
    (Intermediate c r)
    (HasReply c r)
validateReplyFor c r = Nothing

export
||| Read an S-expression from the socket
|||
||| requires socket is connected to IDE server
receiveSExp :
  (hasIO : HasIO io) =>
  Socket -> io (Either SessionSExpError SExp)
receiveSExp server = do
  Right bits <- recvBytes server 6
  | Left err => pure $ Left $ Socket (PacketCountSocketError, err)
  let Just count = map (cast {from = Integer, to = Int})
                 $ fromHexChars $ map cast bits
  | Nothing => pure $ Left $ Encoding $ PacketSizeParse
                    $ fastPack $ map cast bits
  Right sexpSrcBytes <- recvBytes server count
  | Left err => pure $ Left $ Socket
                     (PacketPayloadSocketError, err)
  let sexpSrc = fastPack $ map cast sexpSrcBytes
  let Right sexp = parseSExp sexpSrc
  | Left err => pure $ Left $ SExpParse err
  pure (Right sexp)

export
||| Read a reply from the socket
recvUntyped :
  (hasIO : HasIO io) =>
  Socket -> io (Either SessionReplyError Reply)
recvUntyped server = do
  Right sexp <- receiveSExp server
  | Left err => pure $ Left $
                PropagateSExp err
  -- TODO: for logging purproses, delete this once finished
  putStrLn """
    recvUntyped:sexp=\{show sexp}
    """
  let Just reply = fromSExp sexp
  | Nothing => pure $ Left $ ParseReply sexp
  pure $ Right reply

matchReply : Integer -> Reply -> Bool
matchReply ident (ProtocolVersion i j) = True
matchReply ident (Immediate x i     ) = ident == i
matchReply ident (Intermediate x i  ) = ident == i
matchReply ident (WriteString str i ) = ident == i
matchReply ident (SetPrompt str i   ) = ident == i
matchReply ident (Warning x str xs i) = ident == i

handleRepliesWith :
  (hasIO : HasIO io) =>
  Socket -> Integer -> (c : IDECommand) ->
  (handler : (r : Reply) ->
             (0 isIntermediate : Intermediate c r) =>
             io (Either SessionError ())) ->
  io (Either SessionError (Subset Reply (HasReply c)))
handleRepliesWith server ident c handler = do
  Right reply <- recvUntyped server
  | Left err => pure $ Left $ PropagateReply c err
  let True = matchReply ident reply
  | False => pure $ Left
           $ MessageIdentifierMismatch c reply ident
  case validateReplyFor c reply of
    Nothing => do
      putStrLn """
        Oopsy! Unexpected reply:
          issued: \{show $ toSExp c}
          received: \{show $ toSExp reply}
        """
      pure $ Left $ UnexpectedReply c reply
    Just (Left interm) => do
      Right () <- handler reply
      | Left err => pure $ Left err
      handleRepliesWith server ident c handler
    Just (Right result) => pure $ Right (Element reply result)


send : (hasIO : HasIO io) => Server version Ready ->
  (c : IDECommand) ->
  ((r : Reply) ->
    (0 isIntermediate : Intermediate c r) =>
    io (Either SessionError ())) ->
  io (Either SessionError (Subset Reply (HasReply c)))
send server c handler = do
  let (ident, server') = bump server
  let r = show (SExpList [toSExp c, IntegerAtom ident]) ++ "\n"
      msg = leftPad '0' 6 (asHex (cast (length r)))
            ++ r
  Right rc <- send server'.socket msg
  | Left err => do
      close server'.socket
      pure $ Left
           $ SendPropagateSocketError c msg err
  handleRepliesWith server'.socket ident c handler

export
||| Connect to the IDE server
||| Consider using `connectWith` and passing a call-back
||| to avoid keeping the server open
connect :
  (hasIO : HasIO io) =>
  Port ->
  {default (Hostname "localhost")
    address : SocketAddress}->
  io (Either SessionError
       (version : IDEProtocolVersion ** Server version Ready))
connect port = do
  Right server <- socket AF_INET Stream 0
  | Left err => pure $ Left $ Connection address port
                     $ SocketFailure AF_INET Stream 0 err
  0 <- connect server address port
  | errCode => do close server
                  pure $ Left $ Connection address port
                       $ ConnectionFailure errCode
  Right sexp <- receiveSExp server
  | Left err => do
              close server
              pure $ Left $ Connection address port
                   $ ConnectionPropagateSExp err
  let Just (ProtocolVersion major minor)
        = fromSExp {a = Reply} sexp
  | Just reply => do
      close server
      pure $ Left $ Connection address port
           $ HandshakeUnexpected reply
  | Nothing => do
      close server
      pure $ Left $ Connection address port
           $ HandshakeParseError sexp
  pure $ Right (MkIDEProtocolVersion major minor **
    (MkServer server 0))

||| Connect to the IDE server and execute the given session
||| Ensures the server is closed at the end of the session
connectWith :
  (hasIO : HasIO io) =>
  Port ->
  {default (Hostname "localhost")
    address : SocketAddress}->
  (session :
    {version : IDEProtocolVersion} -> Server version Ready ->
  io (Either SessionError a)) ->
  io (Either SessionError a)
connectWith port session = do
  Right (_ ** server) <- Session.connect {address} port
  | Left err => pure $ Left err
  result <- session server
  close server.socket
  pure result


response : String
response = #"(:output (:ok (:highlight-source ((((:filename "src/Protocol/IDE/Session.idr") (:start 0 0) (:end 0 6)) ((:decor :keyword)))))) 1)"#
test : Maybe Reply
test = either (const Nothing) fromSExp $ parseSExp response
