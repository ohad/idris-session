module Protocol.IDE.Session

import Network.Socket
import Network.Socket.Data
import Network.Socket.Raw

import Protocol.Hex

import System

import Protocol.IDE

{- The server's state machine:

  start
    | RECV: protocol-version        RECV: response1 : r.Response
   v                              v-------+
  READY --- SEND: request r --> PROCESSING r -+
   ^_______________________________|
      RECV :return :ok, :error
-}

data ServerState = Ready | Processing IDECommand | Done

Server : IdrisVersion -> ServerState -> Type

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
  close server
  pure {f = IO} ()
