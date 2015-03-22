-- | ProtoQuipper uses a stack of reader monads in order to alleviate the complexity of a unique
-- state moned. The core monad includes the basic objects that will be used all along the translation.
-- Other monad will be added on top of this one, each adding more possibilities.

module Monad.Core where

-- | A data type to implement a logger. Logs can be given different priorities, depending on their
-- importance. Any log whose priority is lower than the verbose control is discarded. The logs are
-- printed to a channel, which can be, for example, 'stdout', 'stderr', or any file writing channel.
data Logfile = Logfile {
  channel :: Handle,          -- ^ The output channel, by default stdout.
  verbose :: Int,             -- ^ The verbose level, by default nul.
  warnings :: String          -- ^ Handling of warnings (error, print, ignore).
}

-- | The core monad keeps track of module information, and contains all module dependencies. 
data CoreState = State {
  
}

type Core a = ReaderT CoreState IO a


---------------------------------------------------------------------------------------------------
-- * Logger

-- | Log a message with a given priority level.
log :: Int -> String -> Core ()
log lvl msg = do
  logfile <- asks logfile
  w <- liftIO $ hIsWritable $ channel logfile
  if lvl >= verbose logfile || not w then
    return ()
  else do
    liftIO $ hPutStrLn (channel logfile) msg
    liftIO $ hFlush (channel logfile)


-- | Display a warning. The verbose level is ignored. If the option \'Werror\' was added, all warnings
-- are raised as errors.
warning :: Warning -> Maybe Extent -> Core ()
warning warn ex = do
  logfile <- asks logfile
  w <- liftIO $ hIsWritable $ channel logfile
  if not w then
    return ()
  else do
    let waction = warnings logfile
    if waction == "display" then
      case ex of
        Just ex -> liftIO $ hPutStrLn (channel logfile) $ printE warn ex
        Nothing -> liftIO $ hPutStrLn (channel logfile) $ printE warn extent_unknown
    else if waction == "error" then
      Q.throw warn ex
    else
      return ()
    liftIO $ hFlush (channel logfile)
