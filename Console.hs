{-# LANGUAGE CPP #-}

-- | Because mgwin32 doesn't support all the console operations used under linux,
-- it is necessary to provide replacements to these particular operations.
-- Are concerned:
--
-- * all the operations imported from the System.Console.ReadLine library, which library
--   is not easily available under windows (and not necessary either, since the purpose of this library, ie command history, is
--   naturally enforced).
--
-- * color display. It is simply removed then.
--
module Console where

import Monad.QpState

import System.IO

#if mingw32_HOST_OS
#else
import System.Console.Readline
#endif


-- | Definition of some colors.
data Color = Red | Yellow | Blue


-- | Waits for a user command.
--
-- * Under linux, this is implemented by a call to the function readline of the System.Console.ReadLine module.
--
-- * Under windows, this is simply a call to the getLine function from the System.IO module. The shell already
--   provides an historic.
--
prompt :: String                  -- ^ A prompt string, like "# " or "$ ".
       -> QpState (Maybe String)  -- ^ A command line.


-- | Adds a command to the history.
--
-- * Under linux, this is a call to the function addHistory of the System.Console.ReadLine module.
-- 
-- * Under windows, this function does nothing.
--
add_history :: String -> QpState ()


-- | Displays colored text. Again, this function is a simple call to putStr under windows.
putStrC :: Color -> String -> QpState ()


-- | Same as putStrC, expect that the used function is putStrLn instead of putStr.
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

