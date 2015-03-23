{-# LANGUAGE ScopedTypeVariables #-}

-- | This module defines the command line options.
module Options where

import System.Console.GetOpt
import System.Exit
import System.Directory

import qualified Control.Exception as E
import qualified Data.List as List

-- | A data structure to hold command line options.
data Options = Options {
  verbose :: Int,                   -- ^ The verbose level (default: -1).
  warning_action :: String,         -- ^ How should warnings be handled (default: \"display\").

  includes :: [FilePath],           -- ^ List of include directories (default: empty).

  exact :: Bool,                    -- Switch on / off the use of approximations in the unification algorithm.

  run_interpreter :: Bool,          -- ^ Interpret the code? (default: yes).
  run_compiler :: Bool,             -- ^ Compile the code? (default: no).

  conversion_format :: String,      -- ^ Select the conversion to apply (e.g.: "cps", "wcps") (default: "wcps").
  show_intermediate :: Bool,        -- ^ Should the intermediate code be displayed ?
  output_dir :: String,             -- ^ Where should the bitcode files be created ?

  circuit_format :: String          -- ^ The circuit output format (ignore for other values) (default: \"ir\").
} deriving Show


-- | The default set of options.
default_options :: Options
default_options = Options {
  -- General options
  verbose = 0,
  warning_action = "display",

  -- Include directories
  includes = [],

  -- Settings
  exact = True,

  -- Actions
  run_interpreter = True,
  run_compiler = False,
  conversion_format = "wcps",
  show_intermediate = False,
  output_dir = ".",

  -- Others
  circuit_format = "ir"
}


-- | Link the actual command line options to modifications of
-- the option state.
options :: [OptDescr (Options -> IO Options)]
options =
  [ Option ['h'] ["help"] (NoArg show_help)
      "show usage info and exit",
    Option ['V'] ["version"] (NoArg show_version)
      "show version info and exit",
    Option ['v'] ["verbose"] (OptArg read_verbose "LEVEL")
      "enable verbose output",
    Option ['W'] [] (ReqArg read_warning "ATTR")
      "specify the handling of warnings. Possible actions are 'error', 'hide', 'display' (default).",
    Option ['I'] ["include"] (ReqArg include_directory "DIR")
      "add a directory to the module path",
    Option ['r'] ["run"] (NoArg (\opts -> return opts { run_interpreter = True }))
      "run the interpreter (default)",
    Option ['t'] ["type"] (NoArg (\opts -> return opts { run_interpreter = False }))
      "type-checking only; don't run the interpreter",
    Option [] ["exact"] (ReqArg (\b opts -> return opts { exact = read b }) "[True False]")
      "allow for approximations in the unification process",
    Option ['f'] ["format"] (ReqArg read_format "FORMAT")
      "set the output format for circuits. Valid formats are 'ir' (default), 'visual'.",
    Option ['c'] ["compile"] (OptArg read_conversion "CONV")
      "run the compiler, with a specified conversion. Possible conversions are 'cps' and 'wcps'",
    Option ['o'] ["output"] (ReqArg read_output "DIR")
      "specify the output directory of the compilation",
    Option [] ["show-intermediate"] (ReqArg (\b opts -> return opts { show_intermediate = read b }) "[True False]")
      "show the intermediate code produced by the compiler"
  ]


-- | Return True if and only if the @run_interpret@ flag is set, and @run_compiler@ is not.
run_interpret :: Options -> Bool
run_interpret opts =
  run_interpreter opts && not (run_compiler opts)


-- | Display the help screen, and exit.
show_help :: Options -> IO a
show_help _ = do
  putStrLn $ usageInfo header options
  exitSuccess


-- | Show the version number, and exit.
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


-- | Read a verbosity level and update the option vector.
-- If the level is something other than an integer, fail via a call to 'optFail'.
read_verbose :: Maybe String -> Options -> IO Options
read_verbose n opts =
  case n of
    Just n ->
        case reads n of
          [(v, "")] -> return $ opts { verbose = v }
          _ -> optFail $ "-v: Invalid argument '" ++ n ++ "'"
    Nothing ->
        return $ opts { verbose = 5 }


-- | Read a circuit format and update the option vector.
-- The format must be supported, and supported formats are \"visual\"and \"ir\".
-- All other cases cause the parsing to fail.
read_format :: String -> Options -> IO Options
read_format f opts =
  let formats = ["visual", "ir"] in
  case prefix_of f formats of
    [] -> optFail $ "-f: Invalid format '" ++ f ++ "'"
    [format] -> return $ opts { circuit_format = format }
    _ -> optFail $ "-f: Ambiguous format '" ++ f ++ "'"



-- | Read the warning handler.
-- The action must be supported, and supported actions are \"error\", \"hide\" and \"display\".
-- All other cases cause the parsing to fail.
read_warning :: String -> Options -> IO Options
read_warning f opts =
  let actions = ["error", "hide", "display"] in
  case prefix_of f actions of
    [] -> optFail $ "-W: Invalid action '" ++ f ++ "'"
    [action] -> return $ opts { warning_action = action }
    _ -> optFail $ "-W: Ambiguous action '" ++ f ++ "'"


-- | Read the conversion format.
read_conversion :: Maybe String -> Options -> IO Options
read_conversion Nothing opts =
  return opts { run_compiler = True }
read_conversion (Just f) opts =
  let formats = ["cps", "wcps"] in
  case prefix_of f formats of
    [] -> optFail $ "-c: Invalid conversion '" ++ f ++ "'"
    [format] -> return $ opts { run_compiler = True, conversion_format = format }
    _ -> optFail $ "-c: Ambiguous conversion '" ++ f ++ "'"


-- | Add a directory to the list of include directories. This first checks the existence of the directory,
-- and fails if it doesn't exist.
include_directory :: String -> Options -> IO Options
include_directory dir opts = do
  exist <- doesDirectoryExist dir
  if exist then
    return $ opts { includes = dir:(includes opts) }
  else
    optFail $ "-i: Invalid directory '" ++ dir ++ "'"


-- | Read the output directory.
read_output :: String -> Options -> IO Options
read_output dir opts = do
  exist <- doesDirectoryExist dir
  if exist then
    return opts { output_dir = dir }
  else
    optFail $ "-o: Invalid directory '" ++ dir ++ "'"



-- | The header of the help screen.
header :: String
header = "Usage : Quipper [OPTION..] [file]"


-- | The version number.
version :: String
version = "Proto Quipper - v0.1"


-- | Parse a list of string options, and return the resulting option state.
-- Initially, the options are set to the 'Options.default_option' state.
parseOpts :: [String] -> IO (Options, [String])
parseOpts argv =
  case getOpt Permute options argv of
    (o, n, []) -> do
        opts <- List.foldl (\rec o -> do
                              opts <- rec
                              flip id opts o) (return default_options) o
        return (opts, n)
    (_, _, errs) -> ioError (userError (concat errs ++ usageInfo header options))


