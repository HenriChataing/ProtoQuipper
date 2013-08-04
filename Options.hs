-- | Defines the program options.
module Options where

import System.Console.GetOpt

import qualified Data.List as List

-- | Definition of the record type carrying the options.
data Options = Options {
  showHelp :: Bool,                -- ^ Display the help screen.
  showVersion :: Bool,             -- ^ Display the version number.
  verbose :: Int,                  -- ^ Set the verbose level.

  approximations :: Bool,          -- ^ If the unifier should make approximations.
  workWithProto :: Bool,           -- ^ Unsugar the code.

  includes :: [FilePath],          -- ^ Add a ditrectory to the list of includes.
 
  runUnify :: Maybe String,        -- ^ Run a unification test on the constraint set given as argument.
  runInterpret :: Bool             -- ^ Run the code.
} deriving Show


-- | Default set of options. By default, quipper only runs the type inference algorithm,
-- with no approximations during the unification, and no include directories.
default_options :: Options
default_options = Options {
  -- General options
  showHelp = False,
  showVersion = False,
  verbose = -1,
  
  -- Include directories
  includes = ["qlib/"],

  -- Typing options
  approximations = False,
  workWithProto = False,

  -- Actions
  runUnify = Nothing,
  runInterpret = False
}


-- | Link the actual command line options to modifications of
-- the option state. 
options :: [OptDescr (Options -> Options)]
options =
  [ Option ['h'] ["help"] (NoArg (\opts -> opts { showHelp = True }))
      "Display this screen",
    Option ['V'] ["version"] (NoArg (\opts -> opts { showVersion = True }))
      "Output version information",
    Option ['v'] ["verbose"] (OptArg (\lvl opts -> let n = case lvl of
                                                             Just n -> (read n) :: Int
                                                             Nothing -> 5 in
                                                   opts { verbose = n }) "LEVEL")
      "Enable lavish output",
    Option ['i'] ["include"] (ReqArg (\s opts -> opts { includes = (s ++ "/"):(includes opts) }) "DIR")
      "Include a directory",
    Option ['r'] ["run"] (NoArg (\opts -> opts { runInterpret = True }))
      "Run the interpret",
    Option []    ["approx"] (NoArg (\opts -> opts { approximations = True }))
      "Authorize approximations in unfication algorithm",
    Option []    ["proto"] (NoArg (\opts -> opts { workWithProto = True }))
      "Remove all syntactic sugars",
    Option ['u'] ["unify"] (ReqArg (\s opts -> opts { runUnify = Just s }) "SET")
      "Run the unification algorithm on the constraint set SET"
  ]


-- | The header of the help screen.
header :: String
header = "Usage : Quipper [OPTION..] [file]"


-- | The version number.
version :: String
version = "Proto Quipper - v0.1"


-- | Parses a list of string options, and returns the resulting option state.
-- Initially, the options are set to the default_option state.
parseOpts :: [String] -> IO (Options, [String])
parseOpts argv =
  case getOpt Permute options argv of
    (o, n, []) -> return $ (List.foldl (flip id) default_options o, n)
    (_, _, errs) -> ioError (userError (concat errs ++ usageInfo header options))

