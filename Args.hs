{-
   This module provides a monad dedicated to option parsing.
   
   Parserion actions act on external data, and each option is associated
   with a continuation of the parser
-}
module Args where

import Data.Map as Map

---------------------------------------------------------------------
-- Definition of the arguments parser
  -- The definition is parametrized by an option state definition a, which registers the
  -- current options, and is indepentdent from the rest of the parser

data Parser a =
  Parser {
    -- Parser
    options :: a,

    -- Parse actions
    parse_actions :: Map String (ParseResult a ()),
    default_action :: String -> ParseResult a (),

    -- Unparsed options 
    unparsed :: [String]
  }

newtype ParseResult a b = ParseState (Parser a -> (Parser a, b))

instance Monad (ParseResult a) where
  return a = ParseState (\opt -> (opt, a))
  ParseState run >>= action = ParseState (\opt -> let (opt', a) = run opt in
                                        let ParseState run' = action a in
                                        run' opt')                            

---------------------------------------------------------------------
-- Definition of the options

-- Define a new parse action : when parsing .. , do ..
when_parse :: String -> ParseResult a () -> ParseResult a ()
when_default :: (String -> ParseResult a ()) -> ParseResult a ()
----------------------------------------------------------
when_parse s action = ParseState (\opt -> (opt { parse_actions = Map.insert s action $ parse_actions opt }, ()))
when_default action = ParseState (\opt -> (opt { default_action = action }, ()))


-- Actions on option state
apply :: (a -> a) -> ParseResult a ()
-----------------------------------
apply f = ParseState (\opt -> (opt { options = f $ options opt }, ()))


-- Parser string list management
from_list :: [String] -> ParseResult a ()  -- Set up the unparsed option list
peek :: ParseResult a String
next :: ParseResult a String
is_empty :: ParseResult a Bool
is_tag :: String -> ParseResult a Bool   -- See if the string matches an option tag
revert :: String -> ParseResult a ()
----------------------------------
from_list l = ParseState (\opt -> (opt { unparsed = l }, ()))
peek = ParseState (\opt -> case unparsed opt of
                        [] -> error "Empty option list"
                        op:_ -> (opt, op))
next = ParseState (\opt -> case unparsed opt of
                       [] -> error "Empty option list"
                       op:cop -> (opt { unparsed = cop }, op))
is_empty = ParseState (\opt -> (opt, unparsed opt == []))
is_tag s = ParseState (\opt -> (opt, Map.member s $ parse_actions opt))
revert op = ParseState (\opt -> (opt { unparsed = op:(unparsed opt) }, ()))


----------------------------------------------------------------------
-- Parsing

-- Lookup the appropriate action for the option tag s
assoc_action :: String -> ParseResult a (ParseResult a ())
-- Parse the whole list
parse_options :: ParseResult a ()
---------------------------------
assoc_action s =
  ParseState (\opt -> case Map.lookup s $ parse_actions opt of
                   -- If an option tag is associated
                   Just act -> (opt, act)
                   -- If not, apply the default action to the given string
                   Nothing -> (opt, default_action opt s))

parse_options = do
  end <- is_empty
  if end then
    return ()
  else do
    -- Parse the next option
    opt <- next
    act <- assoc_action opt 
    act
    -- Parse the rest of the options
    parse_options

------------------------------------------------------------------------
-- Main function

-- Initial state of the parser
init_state :: a -> [String] -> Parser a
---------------------------------------
init_state opt l =
  Parser {
    options = opt,

    parse_actions = Map.empty,
    default_action = (\s -> return ()),   -- Do nothing on default

    unparsed = l
  }

-- Run the parser
  -- First arg is the default option state
  -- Second arg is the list of options
  -- Third arg is the definition of the associated actions
run_parser :: a -> [String] -> ParseResult a () -> a
--------------------------------------------------
run_parser opt l actions =
  -- Parsing process
  let ParseState run = do
      -- Set the actions
      actions
      -- Run the parser
      parse_options
  in

  -- Initial state
  let init = init_state opt l in

  -- Run
  let (p, _) = run init in

  -- Return the options
  options p


------------------------------------------------------------------------
-- Generic option state

-- TODO : define some generic option state
