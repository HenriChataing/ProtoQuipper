module Options where

import System.Console.GetOpt

import qualified Data.List as List

data Options = Options {
  showHelp :: Bool,
  showVersion :: Bool,
  verbose :: Int, 

  withConstraints :: Bool,
  approximations :: Bool,
  workWithProto :: Bool,

  includes :: [FilePath],
 
  runUnify :: Maybe String,
  runInterpret :: Bool,
  outputFile :: Maybe String
} deriving Show

defaultOptions = Options {
  -- General options
  showHelp = False,
  showVersion = False,
  verbose = -1,
  
  -- Include directories
  includes = [],

  -- Typing options
    -- Make use of the typing constraints  (e :: T)
  withConstraints = False,
    -- Authorize approximations in unification
  approximations = False,
    -- Remove ALL syntactic sugars, giving raw proto quipper code
  workWithProto = False,

  -- Actions
    -- Run the unification algorithm on a chosen set of constraints
  runUnify = Nothing,
    -- Run the interpret
  runInterpret = False,

  -- Output specification
  outputFile = Nothing
}

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
    Option []    ["constr"] (NoArg (\opts -> opts { withConstraints = True }))
      "Make use of typing constraints (e :: T)",
    Option []    ["approx"] (NoArg (\opts -> opts { approximations = True }))
      "Authorize approximations in unfication algorithm",
    Option []    ["proto"] (NoArg (\opts -> opts { workWithProto = True }))
      "Remove all syntactic sugars",
    Option ['u'] ["unify"] (ReqArg (\s opts -> opts { runUnify = Just s }) "SET")
      "Run the unification algorithm on the constraint set SET",
    Option ['o'] [] (ReqArg (\f opts -> opts { outputFile = Just f }) "FILE")
      "Redirect the output to the file FILE"
  ]

header = "Usage : Quipper [OPTION..] [file]"
version = "Proto Quipper - v0.1"

parseOpts :: [String] -> IO (Options, [String])
-----------------------------------------------
parseOpts argv =
  case getOpt Permute options argv of
    (o, n, []) -> return $ (List.foldl (flip id) defaultOptions o, n)
    (_, _, errs) -> ioError (userError (concat errs ++ usageInfo header options))

