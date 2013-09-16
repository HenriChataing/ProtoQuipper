{-# LANGUAGE CPP #-}

-- | Because the mingw32 environment under Windows does not support
-- all the console operations used under Linux, we provide
-- replacements for these particular operations. The operations in question are:
-- 
-- * All the operations imported from the "System.Console.ReadLine" library, because this library 
--   is not easily available under Windows (and not necessary either, since the purpose of this library, i.e., to supply a command history in interactive mode, already works natively under Windows).
-- 
-- * Color display. In Windows, we simply print in black and white.
-- 
module Console where

import Monad.QpState

import System.IO

#if mingw32_HOST_OS
import GHC.ConsoleHandler
#else
import System.Console.Readline
import System.Posix.Signals
#endif


-- | A data type to define some colors.
data Color = Red | Yellow | Blue


-- | Waits for a user command.
--
-- * Under Linux, this is implemented by a call to the function 'readline' of the "System.Console.ReadLine" module.
--
-- * Under Windows, this is simply a call to the 'getLine' function from the "System.IO module". The shell already
--   provides a history.
--
prompt :: String                  -- ^ A prompt string, like \"# \" or \"$ \".
       -> QpState (Maybe String)  -- ^ A command line.


-- | Catch the interrupt (C-c) signal.
catch_interrupt :: QpState a   -- ^ The code to be executed.
                -> QpState ()  -- ^ The action to follow if the interrupt signal is caught.
                -> QpState a


-- | Adds a command to the history.
--
-- * Under Linux, this is a call to the function 'addHistory' of the "System.Console.ReadLine" module.
-- 
-- * Under Windows, this function does nothing.
--
add_history :: String -> QpState ()


-- | Displays colored text. Under Windows, this is a simple call to 'putStr'.
putStrC :: Color -> String -> QpState ()


-- | Like 'putStrC', but append a newline to the end of the line. 
putStrLnC :: Color -> String -> QpState ()



-- Windows or not Windows, that is the question...
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

catch_interrupt code action =
  QpState { runS = (\ctx -> do
                      oldhandler <- installHandler (Catch $ \event -> do
                                                              if event == ControlC then do
                                                                runS action ctx
								return ()
                                  				else
                                                                return ())
                      res <- runS code ctx
                      installHandler oldhandler
                      return res
 ) }
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

catch_interrupt code action =
  QpState { runS = (\ctx -> do
                      oldhandler <- installHandler keyboardSignal (Catch $ runS action ctx >>= return . snd) Nothing
                      res <- runS code ctx
                      installHandler keyboardSignal oldhandler Nothing
                      return res) }

#endif

