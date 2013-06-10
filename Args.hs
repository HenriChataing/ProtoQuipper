{-
   This module provides a monad dedicated to argion parsing.
   
   Parserion actions act on external data, and each argion is associated
   with a continuation of the parser
-}
module Args where

import Data.Map as Map

---------------------------------------------------------------------
-- Definition of the arguments parser
  -- The definition is parametrized by an argion state definition a, which registers the
  -- current options, and is indepentdent from the rest of the parser

data Args =
  Args {
    -- Parser
    bool_options :: Map String Bool,
    int_options :: Map String Int,
    string_options :: Map String String,

    -- Parse actions
    parse_actions :: Map String (Options ()),
    default_action :: String -> Options (),

    -- Unparsed options 
    unparsed :: [String]
  }

newtype Options a = ArgState (Args -> (Args, a))

instance Monad Options where
  return a = ArgState (\arg -> (arg, a))
  ArgState run >>= action = ArgState (\arg -> let (arg', a) = run arg in
                                        let ArgState run' = action a in
                                        run' arg')                            

class OptionFlag a where
  (<--) :: String -> a -> Options ()
  value :: String -> Args -> a
----------------------------------

instance OptionFlag Bool where
  (<--) s b =
    ArgState (\arg -> (arg { bool_options = Map.insert s b $ bool_options arg }, ()))
  value s args =
    case Map.lookup s $ bool_options args of
      Just b -> b
      Nothing -> error ("Undefined boolean option flag " ++ s)

instance OptionFlag Int where
  (<--) s n =
    ArgState (\arg -> (arg { int_options = Map.insert s n $ int_options arg }, ()))
  value s args =
    case Map.lookup s $ int_options args of
      Just n -> n
      Nothing -> error ("Undefined integer option flag " ++ s)

instance OptionFlag String where
  (<--) s c =
    ArgState (\arg -> (arg { string_options = Map.insert s c $ string_options arg }, ()))
  value s args =
    case Map.lookup s $ string_options args of
      Just c -> c
      Nothing -> error ("Undefined string option flag " ++ s)

---------------------------------------------------------------------
-- Option definition
when_parse :: String -> Options () -> Options ()
when_default :: (String -> Options ()) -> Options ()
----------------------------------------------------
when_parse s cont =
  ArgState (\arg -> (arg { parse_actions = Map.insert s cont $ parse_actions arg}, ()))
when_default act =
  ArgState (\arg -> (arg { default_action = act }, ()))


-- Parser string list management
from_list :: [String] -> Options ()  -- Set up the unparsed argion list
peek :: Options String
next_arg :: Options String
is_empty :: Options Bool
is_tag :: String -> Options Bool   -- See if the string matches an option tag
revert :: String -> Options ()
----------------------------------
from_list l = ArgState (\arg -> (arg { unparsed = l }, ()))
peek = ArgState (\arg -> case unparsed arg of
                        [] -> error "Empty argion list"
                        op:_ -> (arg, op))
next_arg = ArgState (\arg -> case unparsed arg of
                       [] -> error "Empty argion list"
                       op:cop -> (arg { unparsed = cop }, op))
is_empty = ArgState (\arg -> (arg, unparsed arg == []))
is_tag s = ArgState (\arg -> (arg, Map.member s $ parse_actions arg))
revert op = ArgState (\arg -> (arg { unparsed = op:(unparsed arg) }, ()))

----------------------------------------------------------------------
-- Parsing

-- Lookup the appropriate action for the argion tag s
assoc_action :: String -> Options (Options ())
-- Parse the whole list
parse_options :: Options ()
---------------------------
assoc_action s =
  ArgState (\arg -> case Map.lookup s $ parse_actions arg of
                   -- If an argion tag is associated
                   Just act -> (arg, act)
                   -- If not, apply the default action to the given string
                   Nothing -> (arg, default_action arg s))

parse_options = do
  end <- is_empty
  if end then
    return ()
  else do
    -- Parse the next argion
    arg <- next_arg
    act <- assoc_action arg 
    act
    -- Parse the rest of the options
    parse_options

------------------------------------------------------------------------
-- Main function

-- Initial state of the parser
init_state :: [String] -> Args
---------------------------------------
init_state l =
  Args {
    bool_options = Map.empty,
    int_options = Map.empty,
    string_options = Map.empty,

    parse_actions = Map.empty,
    default_action = (\s -> return ()),   -- Do nothing on default

    unparsed = l
  }

-- Run the parser
  -- First arg is the default option state
  -- Second arg is the list of options
  -- Third arg is the definition of the associated actions
run_parser :: [String] -> Options () -> Args
----------------------------------------------------
run_parser l actions =
  -- Parsing process
  let ArgState run = do
      -- Set the actions
      actions
      -- Run the parser
      parse_options
  in

  -- Initial state
  let init = init_state l in

  -- Run
  let (p, _) = run init in

  -- Return the options
  p

