-- | This module defines the structural implementation of algebraic types, and contains the definition
-- of the types manipulated by the compiler.

module Compiler.Types where

import Classes
import Utils

import Monad.Compiler
import Monad.Error

import qualified Core.Syntax as C

import Compiler.SimplSyntax
import Compiler.Circuits

import Data.List as List
import Data.Map as Map
import Data.IntMap as IntMap


---------------------------------------------------------------------------------------------------
-- * Type implementation.

-- | Update the tag access function of a type.
--set_tagaccess :: Algebraic -> (Variable -> Expr) -> QpState ()
--set_tagaccess id gettag = do
--  ctx <- get_context
--  set_context ctx { tagaccess = IMap.insert id gettag $ tagaccess ctx }


-- | Return the tag accessor of an algebraic type. If the tag access is undefined,
-- then the function \choose_implementation\ is called to implement it.
getTag :: Variable -> Variable -> Compiler Expr
getTag _typ x = return $ EAccess 0 x


-- | Settle the implementation (machine representation) of all the constructors of an algebraic type.
-- The implementation will depend on the number of constructors and the number of constructors with
-- arguments. This method will decide where the tag should be inserted, as well as the structure of
-- each constructor.
setTypeImplementation :: Variable -> Compiler ()
setTypeImplementation typ = do
  alg <- algebraic_def id
  let (_, datas) = C.definition alg
  case datas of
    -- Cases with one constructor:
    -- The tag is omitted. No definition of the function gettag is needed.
    [(dcon, Just _)] -> do
        update_datacon dcon (\ddef -> Just ddef { C.construct = Right (\e -> e), C.deconstruct = \v -> EVar v })

    [(dcon, Nothing)] ->
        update_datacon dcon (\def -> Just def { C.construct = Left $ EInt 0, C.deconstruct = \v -> EInt 0 })

    -- Cases with several constrcutors
    _ -> do
        -- First thing : count the constructors taking an argument.
        let (with_args, no_args) = List.partition ((/= Nothing) . snd) datas

        List.foldl (\rec (dcon, _) -> do
              rec
              update_datacon dcon (\ddef -> Just ddef { C.construct = Right (\e -> ETuple [EInt (C.tag ddef),e]), C.deconstruct = \v -> EAccess 1 v })
            ) (return ()) with_args
        -- The constructors with no argument are represented by just their tag. The deconstruct function is not needed.
        List.foldl (\rec (dcon, _) -> do
              rec
              update_datacon dcon (\ddef -> Just ddef { C.construct = Left $ ETuple [EInt (C.tag ddef)] })
            ) (return ()) no_args
        -- The tag is the first element of the tuple.
        set_tagaccess id $ \v -> EAccess 0 v
