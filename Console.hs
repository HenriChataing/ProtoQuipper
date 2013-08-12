{-# LANGUAGE CPP #-}

-- | All the console commands that may not work on windows terminals are grouped in this
-- module.
module Console where

import Monad.QpState

import System.IO

#if mingw32_HOST_OS
#else
import System.Console.Readline
#endif


-- | Data type of console colors.
data Color = Red | Yellow | Blue


-- | Wait for a user command, with the prompt given as argument (eg : "# ").
prompt :: String -> QpState (Maybe String)

-- | Add a command to the history.
add_history :: String -> QpState ()

-- | Print some colored text.
putStrC :: Color -> String -> QpState ()
putStrLnC :: Color -> String -> QpState ()

-- Windows or not windows, that is the question...
#ifdef mingw32_HOST_OS

prompt p = do
  liftIO $ putStr p
  liftIO $ hFlush stdout
  l <- liftIO getLine
  return $ Just l

add_history _ =
  return ()

putStrC _ s =
  liftIO $ putStr s

putStrLnC _ s =
  liftIO $ putStrLn s

#else

prompt p =
  liftIO $ readline p

add_history c =
  liftIO $ addHistory c

putStrC c s =
  case c of
    Yellow -> liftIO $ putStr $ "\x1b[33;1m" ++ s ++ "\x1b[0m" 
    Red -> liftIO $ putStr $ "\x1b[31;1m" ++ s ++ "\x1b[0m" 
    Blue -> liftIO $ putStr $ "\x1b[34;1m" ++ s ++ "\x1b[0m" 

putStrLnC c s =
  case c of
    Yellow -> liftIO $ putStrLn $ "\x1b[33;1m" ++ s ++ "\x1b[0m" 
    Red -> liftIO $ putStrLn $ "\x1b[31;1m" ++ s ++ "\x1b[0m" 
    Blue -> liftIO $ putStrLn $ "\x1b[34;1m" ++ s ++ "\x1b[0m" 

#endif

