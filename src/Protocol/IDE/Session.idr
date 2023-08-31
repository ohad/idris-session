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

{- The server's state machine:

  start
    | RECV: protocol-version        RECV: response1 : r.Response
   v                              v-------+
  READY --- SEND: request r --> PROCESSING r -+
   ^_______________________________|
      RECV :return :ok, :error
-}

data ServerState = Ready | Processing IDECommand | Done

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

receiveSExp : Socket -> IO (Either SocketError SExp)
receiveSExp server = do
  Right bits <- recvBytes server 6
  | Left err => ?dealWithMe1
  let Just count = map (cast {from = Integer, to = Int})
                 $ fromHexChars $ map cast bits
  | Nothing => ?dealWithMe2
  Right sexpSrcBytes <- recvBytes server count
  | Left err => ?dealWithMe3
  let sexpSrc = fastPack $ map cast sexpSrcBytes
  let Right sexp = parseSExp sexpSrc
  | Left err => ?dealWithMe4
  pure (Right sexp)

-- TODO: errors...
recvUntyped : Socket -> IO Reply
recvUntyped server = do
  Right sexp <- receiveSExp server
  | Left err => ?dealwithmesometime10
  putStrLn """
    recvUntyped:sexp=\{show sexp}
    """
  let Just reply = fromSExp sexp
  | Nothing => ?dealwithmesometime9
  pure reply

handleRepliesWith : Socket -> (c : IDECommand) ->
  (handler : (r : Reply) ->
             (0 isIntermediate : Intermediate c r) =>
             IO ()) ->
  IO (Subset Reply (HasReply c))
handleRepliesWith server c handler = do
  reply <- recvUntyped server
  case validateReplyFor c reply of
    Nothing => do
      putStrLn """
        Oopsy! Unexpected reply:
          issued: \{show $ toSExp c}
          received: \{show $ toSExp reply}
        """
      exitWith (ExitFailure 1)
    Just (Left interm) => do
      handler reply
      handleRepliesWith server c handler
    Just (Right result) => pure (Element reply result)

-- TODO: switch to hasIO
send : Socket ->
  (c : IDECommand) ->
  ((r : Reply) ->
    (0 isIntermediate : Intermediate c r) =>
    IO ()) ->
  IO (Subset Reply (HasReply c))
send server c handler = do
  let r = show (SExpList [toSExp c, IntegerAtom 1]) ++ "\n"
      msg = leftPad '0' 6 (asHex (cast (length r)))
            ++ r
  putStrLn "Sending: \{msg}"
  Right rc <- send server msg
  | Left err => ?dealwithme188
  handleRepliesWith server c handler

{-
send _ _ = do
  putStrLn "Not yet implemented"
  exitWith (ExitFailure 1)
-}
Server : IdrisVersion -> ServerState -> Type
-- Internal use only
data Session : IdrisVersion -> (pre, post : ServerState) -> Type
  where
  Quit : Session version Ready Done
{-
socketToFile : Socket -> IO (Either String File)
socketToFile (MkSocket f _ _ _) = do
  file <- FHandle <$> primIO (prim__idrnet_fdopen f "r+")
  if !(fileError file)
    then pure (Left "Failed to fdopen socket file descriptor")
    else pure (Right file)
-}


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
  reply <- Session.send server
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
