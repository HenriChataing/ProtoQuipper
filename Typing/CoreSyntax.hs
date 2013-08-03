{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}


-- | Definition of an internal syntax, which consideraly modifies the grammar of types
-- so as to facilitate the working of the type inference algorithm. For more efficiency, all
-- the term and type variables are labelled by a unique id, which serves as reference in maps
-- and other structures.
module Typing.CoreSyntax where

import Classes
import Utils

import Parsing.Localizing
import Parsing.Syntax (RecFlag (..))
import qualified Parsing.Syntax as S

import Data.List as List


-- | Variable is a synonym for Int, which is the type of type variables, as well as term variables.
type Variable = Int


-- | Referenced flags represent references to flag values. A few values are reserved :
--     0 : is the flag equal to zero (meaning not duplicable),
--     1 : is the flag equal to one (meaning duplicable), 
--     -1 : can be either zero or one, for example with types like bool or unit,
--          implicitely equal to !bool and !unit. Typically, the flag constraints
--          where the left or right hand side is -1 are dropped.
--     Any other value is a flag reference.
type RefFlag = Int


-- | The flag 1.
one :: RefFlag
one = 1

-- | The flag 0.
zero :: RefFlag 
zero = 0

-- | The flag with any value.
anyflag :: RefFlag
anyflag = -1


-- | Represent the value a flag can take. Initially, all flags are set to Unknown, except
-- for some imposed to zero or one by the typing rules.
data FlagValue =
    Unknown   -- ^ The value of the flag has not yet be decided.
  | One       -- ^ The value 1.
  | Zero      -- ^ The value 0.
  | Any       -- ^ Any flag value, typically the flag prefix of circ, bool, unit.
  deriving Show

-- | Information relevant to a flag. This contains the flag value, some debug
-- information used to throw detailed exceptions. Eventually, it will also contain
-- various things such as : reversability, control ..
data FlagInfo = FInfo { 
  value :: FlagValue,                              -- ^ The value of the flag

  debug :: Maybe (TypeOf, Extent, Maybe Type)      -- ^ Debug information. The first element is the expression it is type of,
                                                   -- the second the location of the said expression, the third the original type (it is subtree of).
                                                   -- The third one may be used for example on lists : if an eexpression has type 'list int', but
                                                   -- but wad expected of type 'list bool', the typing error will be produced on the types 'int' and 'bool', which
                                                   -- renders it difficult to locate the real error. In this case, the original type will be 'list int'  and the produced
                                                   -- error : 'couldn't unify the type actual 'int' with the expected type 'bool', in the type 'list int'....
}


-- | Description a type as the actual type of an expression / pattern.
data TypeOf =
    ActualOfE Expr           -- ^ It is the actual type of the expression e
  | ActualOfP Pattern        -- ^ It is the actual type of the pattern p
  deriving Show


-- | Access to the debug information of an optional FlagInfo.
mDebug :: Maybe FlagInfo -> Maybe (TypeOf, Extent, Maybe Type)
mDebug inf =
  case inf of
    Just inf -> debug inf
    Nothing -> Nothing




-- | The definition of types distinguishes between linear types (never duplicable) and types,
-- the latter annotated by a exponential flag. The grammar makes it so that the types are annotated
-- every where with flags, to make it simpler for the type inference algorithm. Here is the definition
-- of linear types, which can never be duplicable.
data LinType =
-- Basic types
    TVar Variable              -- ^ a
  | TArrow Type Type           -- ^ T -> U

-- Tensor types
  | TUnit                      -- ^ ()
  | TTensor [Type]             -- ^ (T1 * .. * Tn)

-- Sum types
  | TBool                      -- ^ bool
  | TInt                       -- ^ int
  | TUser String [Type]        -- ^ Algebraic type, parametrized over the variables a1 .. an.

-- Quantum related types
  | TQbit                      -- ^ qbit
  | TCirc Type Type            -- ^ circ (T, U)
  deriving (Show, Eq)


-- | As stated above, type are annotated by flags. The data type also include typing schemes, used
-- for polymorphism.
data Type =
    TBang RefFlag LinType                                  -- ^ !n A
  | TForall [RefFlag] [Variable] ConstraintSet Type        -- ^ A typing scheme : a type is parametrized over the type variables a1 .. an and
                                                           -- the flags f1 .. fk, which must satisfy the constraints of L.
  deriving Show


-- | Remove the flag annotation from a type, returning a linear type.
no_bang :: Type -> LinType
no_bang (TBang _ t) = t


-- | Specification of a user type.
data Typespec = Spec {
  args :: Int,                                             -- ^ The number of type arguments required.

  unfolded :: ([Type], [Type]),                            -- ^ The unfolded defintion of the type, with on the left the type arguments, and on the right the unfolded type
                                                           -- as T1 + .. + Tk where T1 .. Tk are the types of the data constructors.

  subtype :: ([Type], [Type], [TypeConstraint])            -- ^ The result of breaking the constraint {user args <: user args'}. This extension to the subtyping relation
                                                           -- is automatically inferred during the translation to the core syntax.
}



-- | Like variables (term and type), datacons are attributed unique ids.
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
    PJoker                                        -- ^ _
  | PUnit                                         -- ^ ()
  | PVar Variable                                 -- ^ x
  | PTuple [Pattern]                              -- ^ (p1, .. , pn)
  | PDatacon Datacon (Maybe Pattern)              -- ^ Datacon p
  | PLocated Pattern Extent                       -- ^ Located patterns.
  | PConstraint Pattern S.Type                    -- ^ (p <: T)
  deriving Show 



-- | Definition of the core expressions. The core syntax introduces global variables, imported from the dependency modules.
-- Since the global variables are suposed to be duplicable, it was not necessary to overload the typing context with
-- more variables that would are duplicable anyway.
data Expr =
-- STLC
    EVar Variable                                 -- ^ x
  | EGlobal Variable                              -- ^ Global variable from the imported modules.
  | EFun Pattern Expr                             -- ^ fun p -> t
  | EApp Expr Expr                                -- ^ t u

-- Introduction of the tensor
  | EUnit                                         -- ^ ()
  | ETuple [Expr]                                 -- ^ (t1, .. , tn)
  | ELet RecFlag Pattern Expr Expr                -- ^ let [rec] p = e in f

-- Custom union types
  | EBool Bool                                    -- ^ True / False
  | EInt Int                                      -- ^ Integers.
  | EIf Expr Expr Expr                            -- ^ if e then f else g
  | EDatacon Datacon (Maybe Expr)                 -- ^ Datacon e. The argument may or may not be given, the datacons are considered are manipulated as values.
  | EMatch Expr [(Pattern, Expr)]                 -- ^ match e with (p1 -> f1 | .. | pn -> fn)

-- Quantum rules
  | EBox Type                                     -- ^ box[T]
  | EUnbox                                        -- ^ unbox
  | ERev                                          -- ^ rev

-- Unrelated
  | ELocated Expr Extent                          -- ^ Located expressions.
  | EBuiltin String                               -- ^ #builtin s
  | EConstraint Expr S.Type                       -- ^ (e <: T)
  deriving Show



instance PPrint RefFlag where
  genprint _ f _ = pprint f

  sprintn _ 0 = ""
  sprintn _ 1 = "!"
  sprintn _ (-1) = ""
  sprintn _ (-2) = "?"
  sprintn _ n = supervar '!' n

  sprint n = sprintn defaultLvl n
  pprint n = sprintn Inf n


-- | The class of objects of 'kind' type. This includes, of course, the two LinType and Type, but also
-- everything that contains types : TypeConstraint, ConstraintSet, [TypeConstraint] ...
-- The only purpose of this class is to overload the functions listed below.
class KType a where
  free_typ_var :: a -> [Int]                       -- ^ Returns the list of free type variables.
  subs_typ_var :: Int -> LinType -> a -> a         -- ^ Substitutes a type variable by a linear type.
  
  free_flag :: a -> [Int]                          -- ^ Returns the list of flag references.
  subs_flag :: Int -> Int -> a -> a                -- ^ Substitutes a flag reference by another one.


instance KType LinType where
  free_typ_var (TVar x) = [x]
  free_typ_var (TTensor tlist) = List.foldl (\fv t -> List.union (free_typ_var t) fv) [] tlist
  free_typ_var (TArrow t u) = List.union (free_typ_var t) (free_typ_var u)
  free_typ_var (TCirc t u) = List.union (free_typ_var t) (free_typ_var u)
  free_typ_var (TUser _ arg) = List.foldl (\fv t -> List.union (free_typ_var t) fv) [] arg
  free_typ_var _ = []


  subs_typ_var a b (TVar x) | x == a = b
                        | otherwise = TVar x
  subs_typ_var _ _ TUnit = TUnit
  subs_typ_var _ _ TInt = TInt
  subs_typ_var _ _ TBool = TBool
  subs_typ_var _ _ TQbit = TQbit
  subs_typ_var a b (TUser n args) = TUser n $ List.map (subs_typ_var a b) args
  subs_typ_var a b (TArrow t u) = TArrow (subs_typ_var a b t) (subs_typ_var a b u)
  subs_typ_var a b (TTensor tlist) = TTensor $ List.map (subs_typ_var a b) tlist
  subs_typ_var a b (TCirc t u) = TCirc (subs_typ_var a b t) (subs_typ_var a b u)


  free_flag (TVar x) = [x]
  free_flag (TTensor tlist) = List.foldl (\fv t -> List.union (free_flag t) fv) [] tlist
  free_flag (TArrow t u) = List.union (free_flag t) (free_flag u)
  free_flag (TCirc t u) = List.union (free_flag t) (free_flag u)
  free_flag (TUser _ arg) = List.foldl (\fv t -> List.union (free_flag t) fv) [] arg
  free_flag _ = []


  subs_flag n m (TUser typename args) = TUser typename $ List.map (subs_flag n m) args
  subs_flag n m (TArrow t u) = TArrow (subs_flag n m t) (subs_flag n m u)
  subs_flag n m (TTensor tlist) = TTensor $ List.map (subs_flag n m) tlist
  subs_flag n m (TCirc t u) = TCirc (subs_flag n m t) (subs_flag n m u)
  subs_flag _ _ t = t



instance KType Type where
  free_typ_var (TBang _ t) = free_typ_var t
  free_typ_var (TForall _ _ _ t) = free_typ_var t
  subs_typ_var a b (TBang n t) = TBang n (subs_typ_var a b t)

  free_flag (TBang n t) = n:(free_flag t)
  subs_flag n m (TBang p t) =
    let t' = subs_flag n m t in
    if n == p then
      TBang m t'
    else
      TBang p t'




-- | This instance can't be just obtained by deriving Eq in the definition
-- of Type, because of alpha equivalence in the polymorphic types.
instance Eq Type where
  (==) (TBang m t) (TBang n t') = m == n && t == t'
  -- Normally, the alpha equivalence would have to be checked. However, it may
  -- be useless as : this function is never used, the generic instance is always the same, never
  -- changed.
  (==) (TForall _ _ _ typ) (TForall _ _ _ typ') = typ == typ'



instance Param Pattern where
  free_var (PVar x) = [x]
  free_var (PDatacon _ Nothing) = []
  free_var (PDatacon _ (Just p)) = free_var p
  free_var (PTuple plist) = List.foldl (\fv p -> List.union (free_var p) fv) [] plist
  free_var (PConstraint p _) = free_var p
  free_var (PLocated p _) = free_var p
  free_var _ = []

  subs_var _ _ p = p


instance Param Expr where
  free_var (EVar x) = [x]
  
  free_var (EGlobal x) = [x]

  free_var (EFun p e) = 
    let fve = free_var e
        fvp = free_var p in
    fve \\ fvp

  free_var (ELet r p e f) =
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

  free_var (EConstraint e _) =
    free_var e

  free_var _ =
    []

  subs_var _ _ e = e




-- | The subtyping relation <: operates on both linear types and types
-- However, only constraints on types are kept, since it is the kind of constraints generated by the
-- constraint typing algorithm, and it is also useful to have the flag references at hand.
data TypeConstraint =
    Subtype Type Type   -- ^ A sub-typing constraint T <: U
  deriving (Show, Eq)


-- | Shortcut operator for writing sub-typing constraints.
(<:) :: Type -> Type -> TypeConstraint
t <: u = Subtype t u


-- | Another shortcut for writing a set of constraints T1 .. Tn <: U.
(<<:) :: [Type] -> Type -> [TypeConstraint]
tlist <<: u = List.map (\t -> t <: u) tlist


-- | Another shortcut for writing a set of constraints T <: U1 .. Un.
(<::) :: Type -> [Type] -> [TypeConstraint]
t <:: ulist = List.map (\u -> t <: u) ulist



-- | Flag constraints, of the form n <= m, to be interpreted as
--    n <= 0  ==  n :=: 0
--    1 <= n  ==  n :=: 1
--    m <= n  ==  m = 1 => n = 1
type FlagConstraint =
  (RefFlag, RefFlag)


-- | A constraint set contains both subtyping and flag constraints.
type ConstraintSet =
  ([TypeConstraint], [FlagConstraint])


-- | Class of constraints 'sets': the only three instances shall be FlagConstraint and TypeConstraint and ConstraintSet
-- The only purpose of this class is to overload the <> operator to be able to use it on either constaint
-- sets, lists of type constraints, or lists of flag constraints.
class Constraints a b where
  (<>) :: a -> b -> ConstraintSet        -- ^ Concatenation of two constraint sets. This function doesn't check for duplicates.

instance Constraints [TypeConstraint] [TypeConstraint] where
  lc <> lc' = (lc ++ lc', [])

instance Constraints [TypeConstraint] [FlagConstraint] where
  lc <> fc = (lc, fc)

instance Constraints [TypeConstraint] ConstraintSet where
  lc <> (lc', fc') = (lc ++ lc', fc')

instance Constraints [FlagConstraint] [TypeConstraint] where
  fc <> lc = (lc, fc)

instance Constraints [FlagConstraint] [FlagConstraint] where
  fc <> fc' = ([], fc ++ fc')

instance Constraints [FlagConstraint] ConstraintSet where
  fc <> (lc', fc') = (lc', fc ++ fc')

instance Constraints ConstraintSet [TypeConstraint] where
  (lc, fc) <> lc' = (lc ++ lc', fc)

instance Constraints ConstraintSet [FlagConstraint] where
  (lc, fc) <> fc' = (lc, fc ++ fc')

instance Constraints ConstraintSet ConstraintSet where
  (lc, fc) <> (lc', fc') = (lc ++ lc', fc ++ fc')


-- | Empty constraint set.
emptyset :: ConstraintSet
emptyset = ([], [])


-- | Returns true iff the constraint is of the form T <: T.
is_trivial :: TypeConstraint -> Bool
is_trivial (Subtype a b) = a == b


-- | Returns true iff the constraint T <: U is atomic, meaning
-- T and U are both of the form !na where a is a type variable.
is_atomic :: TypeConstraint -> Bool
is_atomic (Subtype (TBang _ (TVar _)) (TBang _ (TVar _))) = True
is_atomic _ = False


-- | Returns true iff the constraint T <: U is composite, meaning
-- it can be reduced by application of one or more of the subtyping
-- relations.
is_composite :: TypeConstraint -> Bool
is_composite c = (not $ is_atomic c) && (not $ is_semi_composite c)


-- | Returns true iff the constraint T <: U is semi composite, meaning
-- it is not atomic, and either T or U is of the form !na, making it not
-- composite.
is_semi_composite :: TypeConstraint -> Bool
is_semi_composite (Subtype t u) =
  case (t, u) of
    (TBang _ (TVar _), TBang _ (TVar _)) -> False
    (TBang _ (TVar _), _) -> True
    (_, TBang _ (TVar _)) -> True
    _ -> False


-- | Returns true iff the constraint is of the form  user n a <: user n a'.
is_user :: TypeConstraint -> Bool
is_user (Subtype t u) =
  case (t, u) of
    (TBang _ (TUser _ _), TBang _ (TUser _ _)) -> True
    _ -> False

-- | Check whether all the constraints of a list have the same property of being right / left sided, ie :
--    - of the form a <: T : left-sided
--    - of the from T <: a : right-sided
--  The function is_right_sided returns true if all the constraints are right sided
--               is_left_sided returns true if all the constraints are left sided
--               is_one_sided returns true if either is_left_sided or is_right_sided is true
--
is_one_sided :: [TypeConstraint] -> Bool
is_one_sided [] = True
is_one_sided ((Subtype t u):cset) =
  case (t, u) of
    (TBang _ (TVar _), _) -> is_left_sided cset
    (_, TBang _ (TVar _)) -> is_right_sided cset
    _ -> False


-- | Checks whether all the type constraints of a list are left sided or not.
is_left_sided :: [TypeConstraint] -> Bool
is_left_sided [] = True
is_left_sided ((Subtype (TBang _ (TVar _)) _):cset) =
  is_left_sided cset
is_left_sided _ = False


-- | Checks whether all the type constraints of a list are right sided or not.
is_right_sided :: [TypeConstraint] -> Bool
is_right_sided [] = True
is_right_sided ((Subtype _ (TBang _ (TVar _))):cset) =
  is_right_sided cset
is_right_sided _ = False


-- | Attempts to link together the input constraints, for example the set { b <: U, a <: b, T <: a } can
--  be rearranged as { T <: a <: b <: U }
--
--  The result is used in the unification algorithm : if the constraints can be linked, the approximation
--    { T <: a <: b <: U }  <=>  a :=: b :=: T, { T <: U } can be made
chain_constraints :: [TypeConstraint] -> (Bool, [TypeConstraint])
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



-- | Try linking the constraints, starting from the left, and progressing by adding constraints
-- on the right.
chain_left_to_right :: [TypeConstraint] -> Int -> [TypeConstraint] -> (Bool, [TypeConstraint])
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


-- | Try linking the constraints, starting from the right, and progressing by adding constraints
-- on the left.
chain_right_to_left :: [TypeConstraint] -> Int -> [TypeConstraint] -> (Bool, [TypeConstraint])
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



-- | Type constraints are also of a kind ktype.
instance KType TypeConstraint where
  free_typ_var (Subtype t u) = List.union (free_typ_var t) (free_typ_var u)
  subs_typ_var a b (Subtype t u) = Subtype (subs_typ_var a b t) (subs_typ_var a b u)

  free_flag (Subtype t u) = List.union (free_flag t) (free_flag u)
  subs_flag n m (Subtype t u) = Subtype (subs_flag n m t) (subs_flag n m u)


-- | .. as are constraint sets.
instance KType ConstraintSet where
  free_typ_var (lc, _) = List.foldl (\fv c -> List.union (free_typ_var c) fv) [] lc
  subs_typ_var a b (lc, fc) = (List.map (subs_typ_var a b) lc, fc)

  free_flag (lc, fc) =
    let ffl = List.foldl (\fv c -> List.union (free_flag c) fv) [] lc
        fff = List.foldl (\fv (n, m) -> List.union [n, m] fv) [] fc in
    List.union ffl fff 

  subs_flag n m (lc, fc) =
    let lc' = List.map (subs_flag n m) lc
        fc' = List.map (\(p, q) -> if p == n then (m, q)
                                   else if q == n then (p, m)
                                   else (p, q)) fc in
    (lc', fc')


-- | Generalize a type, associated with constraints, over its free variables and flags
-- The free variables of the type are those as are superior than or equal to lim type/flag
-- elsewhere.
generalize_type :: Type -> (Variable, RefFlag) -> ConstraintSet -> Type
generalize_type typ (limtype, limflag) cset =
  -- Free variables and flags of the type
  let fvt = free_typ_var typ
      fft = free_flag typ in

  -- Filter the bound variables
  let fvt' = List.filter (\x -> x >= limtype) fvt
      fft' = List.filter (\f -> f >= limflag) fft in

  -- An optimisation would separate the constraints relevant
  -- to the type before generalizing, but later
  TForall fvt' fft' cset typ


