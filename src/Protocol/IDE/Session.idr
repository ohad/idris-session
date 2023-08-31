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

data ServerState = Ready | Processing IDECommand | Done

record Server (version : IdrisVersion) (state : ServerState) where
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
receiveSExp : Socket -> IO (Either SessionSExpError SExp)
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
recvUntyped : Socket -> IO (Either SessionReplyError Reply)
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

handleRepliesWith : Socket -> Integer -> (c : IDECommand) ->
  (handler : (r : Reply) ->
             (0 isIntermediate : Intermediate c r) =>
             IO (Either SessionError ())) ->
  IO (Either SessionError (Subset Reply (HasReply c)))
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

-- TODO: switch to hasIO
send : Server version Ready ->
  (c : IDECommand) ->
  ((r : Reply) ->
    (0 isIntermediate : Intermediate c r) =>
    IO (Either SessionError ())) ->
  IO (Either SessionError (Subset Reply (HasReply c)))
send server c handler = do
  let (ident, server') = bump server
  let r = show (SExpList [toSExp c, IntegerAtom ident]) ++ "\n"
      msg = leftPad '0' 6 (asHex (cast (length r)))
            ++ r
  Right rc <- send server'.socket msg
  | Left err => pure $ Left
              $ SendPropagateSocketError c msg err
  handleRepliesWith server'.socket ident c handler

-- Internal use only
data Session : IdrisVersion -> (pre, post : ServerState) -> Type
  where
  Quit : Session version Ready Done

emptySession : Session version Ready Done
emptySession = Quit

connect : Port -> ({version : IdrisVersion} ->
  Session version Ready Done) -> IO ()
connect port session = do
  Right server <- socket AF_INET Stream 0
  | Left err => do putStrLn """
                     Failed to open socket.
                     \{show err}
                     """
                   exitWith (ExitFailure 1)
  0 <- connect server (Hostname "localhost") port
  | errCode => do putStrLn """
                  Failed to bind to Idris server port \{show port}.
                  Error code \{show errCode}.
                  """
                  close server
                  exitWith (ExitFailure 2)
  putStrLn "success!"
  Right sexp <- receiveSExp server
  | Left err => ?dealwithme7
  let Just (ProtocolVersion major minor) = fromSExp {a = Reply} sexp
  | Just repy => ?dealwithme8
  | Nothing => ?dealwithme9
  putStrLn
    """
    Protocol version \{show major}.\{show minor}
    """
  reply <- Session.send (MkServer server 0)
    (LoadFile "src/Protocol/IDE/Session.idr" Nothing)
    --(Interpret ":cwd")
    --(Version)
    (\response => void %search)
  --?help
  close server

response : String
response = #"(:output (:ok (:highlight-source ((((:filename "src/Protocol/IDE/Session.idr") (:start 0 0) (:end 0 6)) ((:decor :keyword)))))) 1)"#
test : Maybe Reply
test = either (const Nothing) fromSExp $ parseSExp response
