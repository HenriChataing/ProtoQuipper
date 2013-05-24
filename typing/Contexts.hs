module Contexts where

import CoreSyntax
import Localizing

import Classes
import Utils

import Data.Map as Map
import Data.List as List

-------------------------
-- Contexts definition --

data Context =
  Ctx {
    -- Map of bindings : Term variable -> Type
    bindings :: Map Int Type,

    -- Type Id generation
    type_id :: Int, 
    -- Flag id generation
    flag_id :: Int
  }
newtype State a = State (Context -> (Context, a))

instance Monad State where
  return a = State (\ctx -> (ctx, a))
  State run >>= action = State (\ctx -> let (ctx', a) = run ctx in
                                        let State run' = action a in
                                        run' ctx')


-- Create an empty context (without the basic gates)
empty_context :: Context
-----------------------
empty_context =
  Ctx { bindings = empty,
        flag_id = 2,   -- Flag ids 0 and 1 are reserved, and represent the values 0 and 1
        type_id = 0
      }

-------------------
-- Id generation --

fresh_type :: State Variable
fresh_flag :: State Flag

-- Generate a type of the form a or !n a 
new_type :: State Type
new_annotated_type :: State Type
---------------------------------------
fresh_type = State (\ctx -> (ctx { type_id = (+1) $ type_id ctx }, type_id ctx))
fresh_flag = State (\ctx -> (ctx { flag_id = (+1) $ flag_id ctx }, flag_id ctx))

new_type = do
  x <- fresh_type
  return (TVar x)
new_annotated_type = do
  x <- fresh_type
  f <- fresh_flag
  return (TExp f $ TVar x)

-----------------
-- Annotating  --

flag_annotations :: State [(Variable, Flag)]
flag_annotations = State (\ctx -> (ctx, Map.foldWithKey (\x t ann -> case t of
                                                                       TExp f _ -> (x, f):ann
                                                                       TUnit -> (x, 1):ann
                                                                       _ -> error ("No flag annotation specified for the type of " ++ subscript ("x" ++ show x)))
                                                        [] $ bindings ctx))

-----------------
-- Bindings    --

bind :: Variable -> Type -> State ()
find :: Variable -> State Type
delete :: Variable -> State ()
filter :: (Variable -> Bool) -> State (Map Variable Type)  -- Select a part of the bindings and return the unselected part
union :: (Map Variable Type) -> State ()
---------------------------------------------------------
bind x t = State (\ctx -> (ctx { bindings = Map.insert x t $ bindings ctx }, ()))
find x = State (\ctx -> (ctx, case Map.lookup x $ bindings ctx of
                                Just t -> t
                                Nothing -> error ("Unbound variable " ++ subscript ("x" ++ show x))))
delete x = State (\ctx -> (ctx { bindings = Map.delete x $ bindings ctx }, ()))
filter f = State (\ctx -> let (ptrue, pfalse) = Map.partitionWithKey (\x _ -> f x) $ bindings ctx in
                          (ctx { bindings = ptrue }, pfalse))
union m = State (\ctx -> (ctx { bindings = Map.union m $ bindings ctx }, ()))


-------------------
-- Some printing --

instance Show Context where
  show ctx = "[| " ++ (Map.foldWithKey (\k t s -> s ++ subscript ("x" ++ show k) ++ " : " ++ pprint t ++ "\n") "" $ bindings ctx) 
 
