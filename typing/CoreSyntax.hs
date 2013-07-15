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


-- | Referenced flags represent references to fla values. A few values are reserved :
--     0 : is the flag equal to zero (meaning not duplicable)
--     1 : is the flag equal to one (meaning duplicable)
--     -1 : can be either zero or one, for example with types like bool or unit,
--          implicitely equal to !bool and !unit. Typically, the flag constraints
--          where the left or right hand side is -1 are dropped
--     any other value is a flag reference
type RefFlag = Int


-- | The flag 1
one :: RefFlag
one = 1

-- | The flag 0
zero :: RefFlag 
zero = 0

-- | The flag with any value
anyflag :: RefFlag
anyflag = -1


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
  deriving Show



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
  | TBool                      -- bool
  | TUser String [Type]                                    -- user type, parametrized over the variables a1 .. an

-- Quantum related types
  | TQbit                      -- qbit
  | TCirc Type Type            -- circ (a, b)

-- Unrelated
  | TLocated LinType Extent    -- t @ ex
  deriving Show


-- | As stated above, type are annotated by flags
data Type =
    TBang RefFlag LinType          -- !n a
  | TForall [RefFlag] [Variable] ConstraintSet Type        -- type parametrized over the variables a1 .. an, the flags f1 .. fk, all satisfying the constraints L
  deriving Show


-- | Remove the flag annotation from a type, returning a linear type
no_bang :: Type -> LinType
no_bang (TBang _ t) = t


-- | Like variables (term and type), datacons are attributed unique ids, which serve to represent them
type Datacon = Int


-- | Definition of the core patterns
-- The definition do not differ much from that of the surface syntax, the only difference lying
-- in variables, now represented by ids.
-- Although the syntax of proto quipper doesn't make use of patterns, keeping them as syntactic sugars
-- reduces the number of variables, since the unsugaring process produces new variables, one for each
-- pair in the pattern :
--
-- Some desugared code :
--  
--    fun p -> e             ==   fun x -> let p = x in e  (and desugared again)
--
--    let <p, q> = e in f    ==   if p, q are variables, then it is a structure of the language
--                                if not, the code :
--                                     let <x, y> = e in
--                                     let p = x in
--                                     let q = y in
--                                     e
--                                (and desugared again)
--

data Pattern =
    PUnit                                         -- <>
  | PVar Variable                                 -- x
  | PTuple [Pattern]                              -- <p1, .. , pn>
  | PDatacon Datacon (Maybe Pattern)              -- datacon p
  | PLocated Pattern Extent                       -- p @ ex
  deriving Show 



-- | Definition of the core expressions

data Expr =
-- STLC
    EVar Variable                                 -- x
  | EFun Pattern Expr                             -- fun p -> t
  | EApp Expr Expr                                -- t u

-- Introduction of the tensor
  | EUnit                                         -- <>
  | ETuple [Expr]                                 -- <t1, .. , tn>
  | ELet Pattern Expr Expr                        -- let p = e in f

-- Custom union types
  | EBool Bool                                    -- True / False
  | EIf Expr Expr Expr                            -- if e then f else g
  | EDatacon Datacon (Maybe Expr)                 -- datacon  - the argument is optinal, as datacons are considered values
  | EMatch Expr [(Pattern, Expr)]                 -- match e with (x1 -> f1 | .. |  xn -> fn)

-- Quantum rules
  | EBox Type                                     -- box[T]
  | EUnbox                                        -- unbox t
  | ERev                                          -- rev

-- Unrelated
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
list_unifier :: [Type] -> Type
------------------------------------
lintype_unifier TUnit _ = TUnit
lintype_unifier _ TUnit = TUnit
lintype_unifier TBool _ = TBool
lintype_unifier _ TBool = TBool
lintype_unifier TQbit _ = TQbit
lintype_unifier _ TQbit = TQbit
lintype_unifier (TUser n app) _ = TUser n app
lintype_unifier _ (TUser n app) = TUser n app
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
  List.foldl (\unif u -> type_unifier unif u) t ct

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
  sprintn _ 0 = ""
  sprintn _ 1 = "!"
  sprintn _ (-1) = ""
  sprintn _ (-2) = "?"
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
  subs_var _ _ TQbit = TQbit
  subs_var a b (TUser n args) = TUser n $ List.map (subs_var a b) args
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


-- | Returns the set of used flag references
free_flag_of_lintype :: LinType -> [RefFlag]
free_flag_of_lintype (TTensor tlist) =
  List.concat $ List.map free_flag tlist

free_flag_of_lintype (TArrow t u) =
  free_flag t ++ free_flag u

free_flag_of_lintype (TCirc t u) =
  free_flag t ++ free_flag u

free_flag_of_lintype _ =
  []

-- | Returns the set of used flag references of a type
free_flag :: Type -> [RefFlag]
free_flag (TBang n t) =
  if n < 2 then
    free_flag_of_lintype t
  else
    n:(free_flag_of_lintype t)


-- | Substitute a flag in a linear type
subs_flag_in_lintype :: RefFlag -> RefFlag -> LinType -> LinType
subs_flag_in_lintype n m (TTensor tlist) = TTensor $ List.map (subs_flag n m) tlist
subs_flag_in_lintype n m (TArrow t u) = TArrow (subs_flag n m t) (subs_flag n m u)
subs_flag_in_lintype n m (TCirc t u) = TCirc (subs_flag n m t) (subs_flag n m u)
subs_flag_in_lintype _ _ t = t


-- | Subtitute a flag reference in the type
-- The function os not defined on typing schemes, it would make no sense
subs_flag :: RefFlag -> RefFlag -> Type -> Type
subs_flag n m (TBang f t) =
  if n == f then
    TBang m $ subs_flag_in_lintype n m t
  else
    TBang f t



instance Param Pattern where
  free_var PUnit = []
  free_var (PVar x) = [x]
  free_var (PDatacon _ Nothing) = []
  free_var (PDatacon _ (Just p)) = free_var p
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

  free_var (EDatacon _ Nothing) = []
  free_var (EDatacon _ (Just e)) = free_var e

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



-- | The subtyping relation <: operates on both linear types and types
-- However, only constraints on types are kept, since it is the kind of constraints generated by the
-- constraint typing algorithm
data TypeConstraint =
    Subtype Type Type
  deriving Show


-- | Flag constraints, of the form n <= m, to be interpreted as
--    n <= 0  ==  n :=: 0
--    1 <= n  ==  n :=: 1
--    m <= n  ==  m = 1 => n = 1
-- However, the constraints n <= 0 and 1 <= m are immediately applied to the reference, or eliminated
type FlagConstraint =
  (RefFlag, RefFlag)


-- | A constraint set contains both subtyping and flag constraints
type ConstraintSet =
  ([TypeConstraint], [FlagConstraint])


-- | Shortcut operator for writing sub-typing constraints
(<:) :: Type -> Type -> TypeConstraint
t <: u = Subtype t u


-- | Concatenation of two constraint sets
(<>) :: ConstraintSet -> ConstraintSet -> ConstraintSet
(lc, fc) <> (lc', fc') = (lc ++ lc', fc ++ fc')


-- | Empty constraint set
emptyset :: ConstraintSet
emptyset = ([], [])

{-
  Constraint properties
    - Atomicity : a constraint is atomic if of the form a <: b
      where a, b are type variables
  
    - Trivial : apply to constraints of the form T <: T or A <: A
      which are solved by reflexivity
 
    - Composite : apply to constraints of the form T <: U
      for any composite types T, U

    - Semi-composite : apply to constraints of the form a <: T or T <: a
      with a a type variable and T a composite type
-}

is_trivial :: TypeConstraint -> Bool
is_atomic :: TypeConstraint -> Bool
is_composite :: TypeConstraint -> Bool
is_semi_composite :: TypeConstraint -> Bool
-------------------------------------------
is_trivial (Subtype a b) = a == b

is_atomic (Subtype (TBang _ (TVar _)) (TBang _ (TVar _))) = True
is_atomic _ = False

is_composite c = (not $ is_atomic c) && (not $ is_semi_composite c)

is_semi_composite (Subtype t u) =
  case (t, u) of
    (TBang _ (TVar _), TBang _ (TVar _)) -> False
    (TBang _ (TVar _), _) -> True
    (_, TBang _ (TVar _)) -> True
    _ -> False


{-
  Check whether all the constraints of a list have the same property of being right / left sided, ie :
    - of the form a <: T : left-sided
    - of the from T <: a : right-sided

  The function is_right_sided returns true if all the constraints are right sided
               is_left_sided returns true if all the constraints are left sided
               is_one_sided returns true if either is_left_sided or is_right_sided is true
-}

is_one_sided :: [TypeConstraint] -> Bool
is_left_sided :: [TypeConstraint] -> Bool
is_right_sided :: [TypeConstraint] -> Bool
---------------------------------------
is_one_sided [] = True
is_one_sided ((Subtype t u):cset) =
  case (t, u) of
    (TBang _ (TVar _), _) -> is_left_sided cset
    (_, TBang _ (TVar _)) -> is_right_sided cset
    _ -> False

is_left_sided [] = True
is_left_sided ((Subtype (TBang _ (TVar _)) _):cset) =
  is_left_sided cset
is_left_sided _ = False

is_right_sided [] = True
is_right_sided ((Subtype _ (TBang _ (TVar _))):cset) =
  is_right_sided cset
is_right_sided _ = False

{-
  Finds the 'most general unifier' (not in the sense of unification) of a list of type constraints.
  The unifier is a type chosen to carry the most information about the structure of the types of the constraints
  (which has to be the same for each type). For example, the chosen unifier of ((a -> b) -> c) and (d -> (e -> f)) is
  ((a -> b) -> (e -> f))

  The list given as argument is assumed to form a 'class' of semi-composite constraints :
    - all the constraints must be semi-composite
    - all the variable of the semi-composite constraints are of the same age class (ie linked together by atomic constraints)
-}
constraint_unifier :: [TypeConstraint] -> Type
-------------------------------------------------
constraint_unifier constraints =
  let comptypes = List.map (\c -> case c of
                                    Subtype (TBang _ (TVar _)) t -> t
                                    Subtype t (TBang _ (TVar _)) -> t) constraints
  in
  list_unifier comptypes

{-
  Attempts to link together the input constraints, for example the set { b <: U, a <: b, T <: a } can
  be rearranged as { T <: a <: b <: U }

  The result is used in the unfication algorithm : if the constraints can be linked, the approximation
    { T <: a <: b <: U }  <=>  a :=: b :=: T, { T <: U } can be made
  (Since if a solution of the approximation can be found, it is also a solution of the initial set, and conversely)
-}
chain_constraints :: [TypeConstraint] -> (Bool, [TypeConstraint])
chain_left_to_right :: [TypeConstraint] -> Int -> [TypeConstraint] -> (Bool, [TypeConstraint])
chain_right_to_left :: [TypeConstraint] -> Int -> [TypeConstraint] -> (Bool, [TypeConstraint])
----------------------------------------------------------------------------------------------
chain_left_to_right chain endvar [] = (True, List.reverse chain)
chain_left_to_right chain endvar l =
  case List.find (\c -> case c of
                          Subtype (TBang _ (TVar y)) _ -> y == endvar
                          _ -> False) l of
    Just c -> case c of
                Subtype (TBang _ (TVar _)) (TBang _ (TVar y)) -> chain_left_to_right (c:chain) y (List.delete c l)
                _ -> if List.length l == 1 then
                       (True, List.reverse (c:chain))
                     else
                       (False, [])
    Nothing -> (False, [])

chain_right_to_left chain endvar [] = (True, chain)
chain_right_to_left chain endvar l =
  case List.find (\c -> case c of
                          Subtype _ (TBang _ (TVar y)) -> y == endvar
                          _ -> False) l of
    Just c -> case c of
                Subtype (TBang _ (TVar y)) (TBang _ (TVar _)) -> chain_right_to_left (c:chain) y (List.delete c l)
                _ -> if List.length l == 1 then
                       (True, c:chain)
                     else
                       (False, [])
    Nothing -> (False, [])

chain_constraints l =
  case List.find (\c -> case c of
                          Subtype (TBang _ (TVar _)) _ -> False
                          _ -> True) l of
    Just c -> case c of
                Subtype _ (TBang _ (TVar y)) -> chain_left_to_right [c] y (List.delete c l)
                _ -> error "Unreduced composite constraint"
  
    Nothing -> case List.find (\c -> case c of
                                       Subtype _ (TBang _ (TVar _)) -> False
                                       _ -> True) l of
                 Just c -> case c of
                             Subtype (TBang _ (TVar y)) _ -> chain_right_to_left [c] y (List.delete c l)
                             _ -> error "Unreduced composite constraint"
                 Nothing -> error "Only atomic constraints"

{-
  Instance declaration

  TypeConstraint is instance of
    - PPrint
    - Param
    - Eq

  FlagConstraint is instance of
    - PPrint

  ConstraintSet is instance of
    - PPrint
-}

instance Param TypeConstraint where
  free_var (Subtype t u) = free_var t ++ free_var u
  subs_var a b (Subtype t u) = Subtype (subs_var a b t) (subs_var a b u)

instance Param ConstraintSet where
  free_var (lc, _) = List.concat $ List.map free_var lc  
  subs_var a b (lc, fc) = (List.map (subs_var a b) lc, fc)

-- | Substitute a flag reference by a new one in a constraint set
subs_flag_in_constraints :: RefFlag -> RefFlag -> ConstraintSet -> ConstraintSet
subs_flag_in_constraints n m (lc, fc) =
  let lc' = List.map (\(Subtype t u) -> Subtype (subs_flag n m t) (subs_flag n m u)) lc
      fc' = List.map (\(p, q) -> if p == n then (m, q)
                                 else if q == n then (p, m)
                                 else (p, q)) fc in
  (lc', fc')


instance Eq TypeConstraint where
  (==) (Subtype t u) (Subtype t' u') = t == t' && u == u'


