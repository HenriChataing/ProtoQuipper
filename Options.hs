{-# LANGUAGE ScopedTypeVariables #-}

-- | Defines the program options.
module Options where

import System.Console.GetOpt
import System.Exit
import System.Directory

import qualified Control.Exception as E
import qualified Data.List as List

-- | Definition of the record type carrying the options.
data Options = Options {
  verbose :: Int,                  -- ^ Set the verbose level.

  approximations :: Bool,          -- ^ If the unifier should make approximations.
  workWithProto :: Bool,           -- ^ Unsugar the code.

  includes :: [FilePath],          -- ^ Add a ditrectory to the list of includes.
 
  runInterpret :: Bool,            -- ^ Run the code.

  circuitFormat :: String          -- ^ Specify the output format of circuits (ignore for other values), default is "ir".
} deriving Show


-- | Default set of options. By default, quipper only runs the type inference algorithm,
-- with no approximations during the unification, and no include directories.
default_options :: Options
default_options = Options {
  -- General options
  verbose = -1,
  
  -- Include directories
  includes = [],

  -- Typing options
  approximations = False,
  workWithProto = False,

  -- Actions
  runInterpret = False,

  -- Others
  circuitFormat = "ir"
}


-- | Link the actual command line options to modifications of
-- the option state. 
options :: [OptDescr (Options -> IO Options)]
options =
  [ Option ['h'] ["help"] (NoArg show_help)
      "Display this screen",
    Option ['V'] ["version"] (NoArg show_version)
      "Output version information",
    Option ['v'] ["verbose"] (OptArg read_verbose "LEVEL")
      "Enable lavish output",
    Option ['i'] ["include"] (ReqArg include_directory "DIR")
      "Include a directory",
    Option ['r'] ["run"] (NoArg (\opts -> return opts { runInterpret = True }))
      "Run the interpret",
    Option []    ["approx"] (NoArg (\opts -> return opts { approximations = True }))
      "Authorize approximations in unfication algorithm",
    Option []    ["proto"] (NoArg (\opts -> return opts { workWithProto = True }))
      "Remove all syntactic sugar",
    Option ['f'] ["format"] (ReqArg read_format "FORMAT")
      "Specify the output format of circuits. Valid formats are 'visual' 'ir'"
  ]


-- | Displays the help screen, and exits.
show_help :: Options -> IO a
show_help _ = do
  putStrLn $ usageInfo header options
  exitSuccess


-- | Shows the version number, and exits.
show_version :: Options -> IO a
show_version _ = do
  putStrLn $ version
  exitSuccess


-- | Called when the parsing of command line arguments fails. The argument is an error message.
optFail :: String -> IO a
optFail msg = do
  putStr msg
  putStrLn " : Try --help for more information"
  exitFailure


-- | Given a list of names, and a string, find all the names it is prefix of.
prefix_of :: String -> [String] -> [String]
prefix_of s names =
  List.filter (List.isPrefixOf s) names


-- | Read and set the verbose level of an option vector.
read_verbose :: Maybe String -> Options -> IO Options
read_verbose n opts =
  case n of
    Just n ->
        case reads n of
          [(v, "")] -> return $ opts { verbose = v }
          _ -> optFail $ "-v: Invalid argument '" ++ n ++ "'"
    Nothing ->
        return $ opts { verbose = 5 }


-- | Read and set the circuit format of an option vector.
read_format :: String -> Options -> IO Options
read_format f opts =
  let formats = ["visual", "ir"] in
  case prefix_of f formats of
    [] -> optFail $ "-f: Invalid format '" ++ f ++ "'"
    [format] -> return $ opts { circuitFormat = format }
    _ -> optFail $ "-f: Ambiguous format '" ++ f ++ "'"


-- | Add a directory to the list of includes.
include_directory :: String -> Options -> IO Options
include_directory dir opts = do
  exist <- doesDirectoryExist dir
  if exist then
    return $ opts { includes = dir:(includes opts) }
  else
    optFail $ "-i: Invalid directory '" ++ dir ++ "'"



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
    (o, n, []) -> do
        opts <- List.foldl (\rec o -> do
                              opts <- rec
                              flip id opts o) (return default_options) o
        return (opts, n)
    (_, _, errs) -> ioError (userError (concat errs ++ usageInfo header options))

