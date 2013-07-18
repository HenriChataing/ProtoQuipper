module Main where

import Parser
import ConstraintParser
import Lexer
import QuipperError
import qualified QpState as Q

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
import qualified Control.Exception as E

import Data.List as List

data Options = Options {
  showHelp :: Bool,
  showVersion :: Bool,
  verbose :: Int, 

  withConstraints :: Bool,
  approximations :: Bool,
  workWithProto :: Bool,
 
  runInterpret :: Bool,
  runTyping :: Bool,
  runUnify :: Maybe String,
  outputFile :: Maybe String
} deriving Show

defaultOptions = Options {
  -- General options
  showHelp = False,
  showVersion = False,
  verbose = -1,
  
  -- Typing options
    -- Make use of the typing constraints  (e :: T)
  withConstraints = False,
    -- Authorize approximations in unification
  approximations = False,
    -- Remove ALL syntactic sugars, giving raw proto quipper code
  workWithProto = False,

  -- Actions
    -- Run the interpreter
  runInterpret = False,
    -- Run the type inference algorithm
  runTyping = False,
    -- Run the unification algorithm on a chosen set of constraints
  runUnify = Nothing,

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
    Option []    ["constr"] (NoArg (\opts -> opts { withConstraints = True }))
      "Make use of typing constraints (e :: T)",
    Option []    ["approx"] (NoArg (\opts -> opts { approximations = True }))
      "Authorize approximations in unfication algorithm",
    Option []    ["proto"] (NoArg (\opts -> opts { workWithProto = True }))
      "Remove all syntactic sugars",
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
          tokens <- mylex "" set
          constraints <- return $ parse_constraints tokens
          (do
             s <- unification_test constraints
             putStrLn s) `E.catch` (\(e :: QError) -> do
                                      putStrLn $ show e)

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
      tokens <- mylex file contents
      prog <- return (parse tokens)
      coreprog <- return $ translate_program prog

      (_, pc) <- Q.runS (coreprog >>= return . pprint) Q.empty_context
      putStrLn pc
      hFlush stdout

      -- Actions
      if runInterpret opts then do
        putStrLn $ "\x1b[1;33m" ++ ">> Interpret" ++ "\x1b[0m" 
        (do
           (_, v) <- Q.runS (coreprog >>= Interpret.run) Q.empty_context
           putStrLn $ pprint v) `E.catch` (\(e :: QError) -> do
                                             putStrLn $ "\x1b[1m" ++ "xx Interpretation failed xx" ++ "\x1b[0m"
                                             putStrLn $ show e)
      else
        return ()

      if runTyping opts then do
        putStrLn $ "\x1b[1;33m" ++ ">> Typing" ++ "\x1b[0m"
        putStrLn $ "\x1b[1m" ++ "TypeInference :" ++ "\x1b[0m"
        (do
           (_, s) <- Q.runS (Q.set_verbose (verbose opts) >> type_inference (not $ approximations opts) prog) Q.empty_context
           putStrLn $ pprint s) `E.catch` (\(e :: QError) -> putStrLn $ show e)
      else
        return ()
  else
    return ()

