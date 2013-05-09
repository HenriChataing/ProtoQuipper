module Contexts where

import CoreSyntax
import Localizing

import Data.Map
import Data.List

-------------------------
-- Various constraints --

type TypeConstraint =         
  (FType, FType, Extent)      -- A = B, the extent is the location of the expression in which the constraint has been generated

cons :: FType -> FType -> Extent -> TypeConstraint
-----------------------------------------------------
cons a b ext = (a, b, ext)

data FlagConstraint =
    FIs Int Int     -- f = 0 | 1
  | FImpl Int Int   -- f = 1 => g = 1
  | FEq Int Int     -- g = g

--------------------
-- Typing schemes --

-- [Int] = list of polymorphic type variables
-- FType = polymorphic type
type Scheme = ([Int], FType)

-- Given a typing scheme, and a set of fresh type variables, generate as many type variables as demanded by the scheme
instanciate :: Scheme -> Context -> (FType, Context)
-----------------------------------------------------
instanciate ([], t) ctx = (t, ctx)
instanciate (fv, t) ctx =
  Data.List.foldl (\(t, ctx) x -> let (nv, ctx') = freshType ctx in
                                  (subst x (TVar nv) t, ctx')) (t, ctx) fv

-------------------------
-- Contexts definition --

data Context =
  Ctx {
    -- Location information
    extent :: Extent,

    -- Map of bindings : Term variable <-> Type
    bindings :: Map Int Scheme,
    
    -- Set of type constraints
    tConstraints :: [TypeConstraint],
    -- Set of flag constraints
    fConstraints :: [FlagConstraint],

    -- Consing of variable names
    fromName :: Map String Int,
    fromId :: Map Int String,

    -- Variable Id generation
    varId :: Int,
    -- Type Id generation
    typeId :: Int, 
    -- Flag id generation
    flagId :: Int
  }

-- Create an empty context (without the basic gates)
emptyContext :: Context
-----------------------
emptyContext = Ctx { extent = extentUnknown,
                     bindings = empty,
                     tConstraints = [],
                     fConstraints = [],
                     fromId = empty,
                     fromName = empty,
                     varId = 0,
                     flagId = 0,
                     typeId = 0 }


-------------------
-- Id generation --

-- Variable id generation
freshVar :: Context -> (Variable, Context)
--------------------------------------
freshVar ctx =
  (Var { uid = varId ctx, ext = extentUnknown }, ctx { varId = (+1) $ varId ctx })

-- Type Id generation
freshType :: Context -> (Int, Context)
---------------------------------------
freshType ctx =
  (typeId ctx, ctx { typeId = (+1) $ typeId ctx })

-- Flag id generation
freshFlag :: Context -> (Int, Context)
--------------------------------------
freshFlag ctx =
  (flagId ctx, ctx { flagId = (+1) $ flagId ctx })

--------------------
-- More functions --

-- Register a variable name
register :: String -> Context -> (Int, Context)
-----------------------------------------------
register s ctx =
  (varId ctx, ctx { varId = (+1) $ varId ctx,
                    fromName = Data.Map.insert s (varId ctx) (fromName ctx),
                    fromId = Data.Map.insert (varId ctx) s (fromId ctx) })

-- Generate a new type variable and associates it iwth a new flag
newType :: Context -> (FType, Context)
--------------------------------------
newType ctx =
  let (v, ctx0) = freshType ctx in
  let (f, ctx1) = freshFlag ctx0 in
  (FTyp (TVar v) f, ctx1)

--------------
-- Bindings --

-- Generate a fresh type variable, and binds it with the variable
bindVariable :: Variable -> Context -> (FType, Context)
----------------------------------------------------
bindVariable x ctx =
  let t = typeId ctx in      -- New type variable
  let f = flagId ctx in      -- New flag
  (FTyp (TVar t) f, ctx { bindings = Data.Map.insert (uid x) ([], FTyp (TVar t) f) $ bindings ctx,
                          typeId = (+1) $ typeId ctx,
                          flagId = (+1) $ flagId ctx })

-- Generate fresh variables enough for a pattern
bindPattern :: Pattern -> Context -> (FType, Context)
----------------------------------------------------------------
bindPattern PUnit ctx =
  let (f, ctx0) = freshFlag ctx in
  (FTyp TUnit f, ctx0)
bindPattern (PVar x) ctx = bindVariable x ctx
bindPattern (PPair p1 p2) ctx =
  let (t1, ctx1) = bindPattern p1 ctx in
  let (t2, ctx2) = bindPattern p2 ctx1 in
  let (f, ctx3) = freshFlag ctx2 in
  (FTyp (TTensor t1 t2) f, ctx3)
-- A constraint is generated binding the inferred type to the given one
bindPattern (PConstraint p typ@(FTyp gtyp g)) ctx =
  let (t@(FTyp ft f), ctx0) = bindPattern p ctx in
  (typ, ctx0 { tConstraints = (cons t typ $ extent ctx):(tConstraints ctx0),
             fConstraints = (FEq f g):(fConstraints ctx0) })

-- Match a pattern with a type and generate the appropriate constraints
matchPattern :: Pattern -> FType -> Context -> ([(Int, FType)], Context)
-------------------------------------------------------------------------
matchPattern PUnit t ctx =
  let (f, ctx0) = freshFlag ctx in
  ([], ctx0 { tConstraints = (cons t (FTyp TUnit f) $ extent ctx):(tConstraints ctx0) })
matchPattern (PVar x) t ctx = ([(uid x, t)], ctx)
-- Since this function is called in let bindings, pattern constraints have yet to be registered
matchPattern (PConstraint p typ) t ctx =
  let (lv, ctx0) = matchPattern p t ctx in
  (lv, ctx0 { tConstraints = (cons t typ $ extent ctx):(tConstraints ctx0) })
-- Not necessary, but avoid generation of useless type variables and constraints
matchPattern (PPair p1 p2) (FTyp (TTensor t1 t2) _) ctx =
  let (lv1, ctx1) = matchPattern p1 t1 ctx in
  let (lv2, ctx2) = matchPattern p2 t2 ctx1 in
  (lv1 ++ lv2, ctx2)
matchPattern (PPair p1 p2) t ctx =
  let (x, ctx0) = newType ctx in
  let (y, ctx1) = newType ctx0 in
  let (lv1, ctx2) = matchPattern p1 x ctx1 in
  let (lv2, ctx3) = matchPattern p2 y ctx2 in
  let (f, ctx4) = freshFlag ctx3 in
  (lv1 ++ lv2, ctx4 { tConstraints = (cons t (FTyp (TTensor x y) f) $ extent ctx):(tConstraints ctx4) })


-------------------
-- Some printing --

instance Show Context where
  show ctx = "{ extent : " ++ (show $ extent ctx) ++
           "\n  bindings :" ++ (Data.Map.foldWithKey (\k v s -> s ++ "(" ++ show k ++ ", " ++ show v ++ ")\n") "" $ bindings ctx) ++
             "  varId : " ++ (show $ varId ctx) ++
           "\n  typeId : " ++ (show $ typeId ctx) ++
           "\n  flagId : " ++ (show $ flagId ctx)
 
