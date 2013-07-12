-- | Definition of an internal syntax, which consideraly modifies the grammar of types
-- so as to facilitate the working of the type inference algorithm. For more efficiency, all
-- the term and type variables are labelled by a unique id, which serves as reference in maps
-- and other structures

module CoreSyntax where

import Classes
import Utils
import Localizing

import Data.List as List



-- | Variable is a synonym for Int, which is the type of type variables, as well as term variables
type Variable = Int


-- | Flags represent flag values. The value of flags can be
--     0 : is the flag equal to zero (meaning not duplicable)
--     1 : is the flag equal to one (meaning duplicable)
--     -1 : can be either zero or one, for example with types like bool or unit,
--          implicitely equal to !bool and !unit. Typically, the flag constraints
--          where the left or right hand side is -1 are dropped
--     -2 : a generic flag, put to fill in gaps in types at the end of a translation, they have to be replaced
--          when using the type
--     any other value : is a flag variable, substituted by one of the vlues above
type RefFlag = Int


-- | Respresent the value a flag can take. Initially, all flags are set to Unknown, except
-- for some imposed to zero or one by the typing rules
data FlagValue =
    Unknown   -- The value of the flag has not yet be decided
  | One       -- The value 1
  | Zero      -- The value 0
  | Any       -- Any flag value, typically the flag prefix of circ, bool, unit


-- | Information relevant to a flag
data FlagInfo = FInfo {
-- The value 
  value :: FlagValue,

-- Information concerning the maybe associated expression
  typeof :: Maybe TypeOf,

-- Location of the expression
  elocation :: Maybe Extent
}


-- | Describe a type
-- A type can fit into several categories : it can be the actual type of a pattern / expr, or
-- the expected type of a pattern / expr
data TypeOf =
-- Actual type
    ActualOfE Expr
  | ActualOfP Pattern
-- Expected type
  | ExpectedOfE Expr
  | ExpectedOfP Pattern
  deriving Show


-- | The flag 1
one :: RefFlag
one = 1

-- | The flag 0
zero :: RefFlag 
zero = 0

-- | The flag with any value
anyflag :: RefFlag
anyflag = -1

-- | The generic flag
genflag :: RefFlag
genflag = -2


-- | The definition of types distinguishes between linear types (never duplicable) and types,
-- the latter annotated by a exponential flag. The grammar makes it so that the types are annotated
-- every where with flags, to make it simpler for the type inference algorithm
-- The division may need to be reviewed in regard of certain type constants like bool,
--  unit, qbit ; flag annotation are unecessary for those constants since bool and unit
--  are automatically duplicable, and qbit can never be such
--
--  Another division would be
--     LinType : TTensor, TArrow
--     Type : TVar, TQbit, TUnit, TCirc (duplicable as well), TBang

data LinType =
-- Basic types
    TVar Variable              -- a
  | TArrow Type Type           -- a -> b

-- Tensor types
  | TUnit                      -- 1
  | TTensor [Type]             -- a1 * .. * an

-- Sum types
  | TUser String               -- user defined type
  | TBool                      -- bool

-- Polymorphism
  | TForall [Variable] Type    -- type generalization
  | TApp Type [Type]           -- generic type instanciation

-- Quantum related types
  | TQbit                      -- qbit
  | TCirc Type Type            -- circ (a, b)

-- Unrelated
  | TLocated LinType Extent    -- t @ ex
  deriving Show


-- | As stated above, type are annotated by flags
data Type =
    TBang RefFlag LinType          -- !n a
  deriving Show



{-
  The pattern structure has been left in the core syntax, although it is a syntactic sugar.
  The code produced by the desugarization would be quite longer

  Note that the desugared code for the following would be :
  
    - fun p -> e   ==>  fun x -> let p = x in e  (and desugared again)

    - let <p, q> = e in f ==> if p, q are variables, then it is a structure of the language
                              if not, the code   let <x, y> = e in
                                                 let p = x in
                                                 let q = y in
                                                 e
-}

type Datacon = Int

data Pattern =
    PUnit                      -- <>
  | PVar Variable              -- x
  | PTuple [Pattern]           -- <p1, .. , pn>
  | PData Datacon Pattern      -- datacon p
  | PLocated Pattern Extent    -- p @ ex
  deriving Show 

{-
  Definition of the expressions, nothing more to say
-}

data Expr =
    EUnit                                         -- <>
  | EBool Bool                                    -- True / False
  | EVar Variable                                 -- x
  | EFun Pattern Expr                             -- fun p -> t
  | ELet Pattern Expr Expr                        -- let p = e in f
  | EApp Expr Expr                                -- t u
  | ETuple [Expr]                                 -- <t1, .. , tn>
  | EIf Expr Expr Expr                            -- if e then f else g
  | EData Datacon Expr                            -- injl e
  | EMatch Expr [(Pattern, Expr)]                 -- match e with (x -> f | y -> g)
  | EBox Type                                     -- box[T]
  | EUnbox                                        -- unbox t
  | ERev                                          -- rev
  | ELocated Expr Extent                          -- e @ ex
  deriving Show

{-
  Construction of the unfier of two / a list of types
  Supposing that the types have the same skeleton, the unifier is the type holding
  the most information about that commin skeleton, eg the unifier of
  (a -> b) -> c and d -> (e * f) would be
  (a -> b) -> (e * f)
-}

lintype_unifier :: LinType -> LinType -> LinType
type_unifier :: Type -> Type -> Type
list_unifier :: [LinType] -> LinType
------------------------------------
lintype_unifier TUnit _ = TUnit
lintype_unifier _ TUnit = TUnit
lintype_unifier TBool _ = TBool
lintype_unifier _ TBool = TBool
lintype_unifier TQbit _ = TQbit
lintype_unifier _ TQbit = TQbit
lintype_unifier (TUser n) _ = TUser n
lintype_unifier _ (TUser n) = TUser n
lintype_unifier (TVar _) t = t
lintype_unifier t (TVar _) = t
lintype_unifier (TArrow t u) (TArrow t' u') = TArrow (type_unifier t t') (type_unifier u u')
lintype_unifier (TTensor tlist) (TTensor tlist') =
  case (tlist, tlist') of
    ([], []) -> (TTensor [])
    (t:rest, t':rest') ->
      let u = type_unifier t t'
          TTensor urest = lintype_unifier (TTensor rest) (TTensor rest') in
      TTensor (u:urest)
lintype_unifier (TCirc t u) (TCirc t' u') = TCirc (type_unifier t t') (type_unifier u u')

type_unifier (TBang m t) (TBang _ u) = TBang m $ lintype_unifier t u

list_unifier (t:ct) =
  List.foldl (\unif u -> lintype_unifier unif u) t ct

{-
  Instance declarations of Flag, LinType, Type, Pattern, Expr :
    - Flag is instance of
      - PPrint

    - LinType is instance of
      - PPrint
      - Param
      - Eq
 
    - Type is instance of
      - PPrint
      - Param
      - Eq

    - Pattern is instance of
      - PPrint
      - Param

    - Expr is instance of
      - PPrint
      - Param
-}

instance PPrint RefFlag where
  sprintn _ n = supervar '!' n
  sprint n = sprintn defaultLvl n
  pprint n = sprintn Inf n



instance Param LinType where
  free_var (TVar x) = [x]
  free_var (TTensor tlist) = List.foldl (\fv t -> List.union (free_var t) fv) [] tlist
  free_var (TArrow t u) = List.union (free_var t) (free_var u)
  free_var (TCirc t u) = List.union (free_var t) (free_var u)
  free_var _ = []

  subs_var a b (TVar x) | x == a = TVar b
                        | otherwise = TVar x
  subs_var _ _ TUnit = TUnit
  subs_var _ _ TBool = TBool
  subs_var a b (TArrow t u) = TArrow (subs_var a b t) (subs_var a b u)
  subs_var a b (TTensor tlist) = TTensor $ List.map (subs_var a b) tlist
  subs_var a b (TCirc t u) = TCirc (subs_var a b t) (subs_var a b u)

instance Eq LinType where
  (==) (TVar x) (TVar y) = x == y
  (==) TUnit TUnit = True
  (==) TBool TBool = True
  (==) TQbit TQbit = True
  (==) (TTensor tlist) (TTensor tlist') = (tlist == tlist')
  (==) (TArrow t u) (TArrow t' u') = (t == t') && (u == u')
  (==) (TCirc t u) (TCirc t' u') = (t == t') && (u == u')
  (==) _ _ = False


instance Param Type where
  free_var (TBang _ t) = free_var t
  subs_var a b (TBang n t) = TBang n (subs_var a b t)

instance Eq Type where
  (==) (TBang m t) (TBang n t') = m == n && t == t'



instance Param Pattern where
  free_var PUnit = []
  free_var (PVar x) = [x]
  free_var (PData _ p) = free_var p
  free_var (PTuple plist) = List.foldl (\fv p -> List.union (free_var p) fv) [] plist
  free_var (PLocated p _) = free_var p

  subs_var _ _ p = p



instance Param Expr where
  free_var (EVar x) = [x]
  
  free_var (EFun p e) = 
    let fve = free_var e
        fvp = free_var p in
    fve \\ fvp

  free_var (ELet p e f) =
    let fve = free_var e
        fvf = free_var f
        fvp = free_var p in
    (List.union fve fvf) \\ fvp

  free_var (EApp e f) =
    List.union (free_var e) (free_var f)

  free_var (ETuple elist) =
    List.foldl (\fv e -> List.union (free_var e) fv) [] elist

  free_var (EIf e f g) =
    List.union (List.union (free_var e) (free_var f)) (free_var g)

  free_var (EData _ e) = free_var e

  free_var (EMatch e blist) =
    let fvlist = List.foldl (\fv (p, f) ->
                               List.union (free_var f \\ free_var p) fv) [] blist
        fve = free_var e in
    List.union fve fvlist
  
  free_var (ELocated e _) =
    free_var e

  free_var _ =
    []

  subs_var _ _ e = e

print_var x = subvar 'x' x


