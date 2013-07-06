module Main where

import Parser
import ConstraintParser
import Lexer

import Classes
import Utils

import Syntax
import Printer

import CoreSyntax
import TransSyntax
import TypingMain

import qualified Interpret
import Values

import System.IO
import System.Environment
import System.Console.GetOpt

import Data.List as List

data Options = Options {
  showHelp :: Bool,
  showVersion :: Bool,
  verbose :: Bool, 
 
  runInterpret :: Bool,
  runTyping :: Bool,
  runUnify :: Maybe String,
  outputFile :: Maybe String
} deriving Show

defaultOptions = Options {
  showHelp = False,
  showVersion = False,
  verbose = False,
  
  runInterpret = False,
  runTyping = False,
  runUnify = Nothing,
  outputFile = Nothing
}

options =
  [ Option ['h'] ["help"] (NoArg (\opts -> opts { showHelp = True }))
      "Display this screen",
    Option ['V'] ["version"] (NoArg (\opts -> opts { showVersion = True }))
      "Output version information",
    Option ['v'] ["verbose"] (NoArg (\opts -> opts { verbose = True }))
      "Enable lavish output",
    Option ['i'] ["interpret"] (NoArg (\opts -> opts { runInterpret = True }))
      "Execute the program received in arguement",
    Option ['t'] ["type"] (NoArg (\opts -> opts { runTyping = True }))
      "Run the type inference algorithm",
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

----------------------------------------------

main = do
  -- Parse program options
  argv <- getArgs
  (opts, files) <- parseOpts argv

  -- Program actions
  if showHelp opts then
    putStrLn $ usageInfo header options
  else
    return ()

  if showVersion opts && not (showHelp opts) then
    putStrLn $ version
  else
    return ()

  if not (showVersion opts) && not (showHelp opts) then do
    -- Unify option
    case runUnify opts of
      Just set -> do
          putStrLn  $ "\x1b[1;33m" ++ ">> unification test" ++ "\x1b[0m"
          constraints <- return $ parse_constraints $ mylex "" $ set
          putStrLn $ test_unification constraints

      Nothing ->
          return ()

    -- Other options
    if files == [] then do
      putStrLn "No argument file specified"
      putStrLn $ usageInfo header options
    else do
      -- For now, only the first file is kept and treated
      -- Read and parse the file
      file <- return $ List.head files
      contents <- readFile file
      prog <- return (parse $ mylex file contents)

      -- Actions
      if runInterpret opts then do
        putStrLn $ "\x1b[1;33m" ++ ">> Interpret" ++ "\x1b[0m" 
        case Interpret.run (drop_constraints prog) of
          Ok v -> do
              putStrLn $ pprint v
          Failed err -> do
              putStrLn $ "\x1b[1m" ++ "xx Interpretation failed xx" ++ "\x1b[0m"
              putStrLn $ show err
      else
        return ()

      if runTyping opts then do
        putStrLn $ "\x1b[1;33m" ++ ">> Typing" ++ "\x1b[0m"
        putStrLn $ "\x1b[1m" ++ "TypeInference :" ++ "\x1b[0m"
        putStrLn $ full_inference prog
      else
        return ()
  else
    return ()
