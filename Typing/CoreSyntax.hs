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


-- | Type of term and type variables.
type Variable = Int


-- | Referenced flags represent references to flag values. A few values are reserved :
--
-- *    0 : is the flag equal to zero (meaning not duplicable),
--
-- *    1 : is the flag equal to one (meaning duplicable), 
--
-- *    -1 : can be either zero or one, for example with types like bool or unit,
--          implicitely equal to !bool and !unit. Typically, the flag constraints
--          where the left or right hand side is -1 are dropped.
--
-- *    Any other value is a flag reference.
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


-- | Represents the value a flag can take. Initially, all flags are set to Unknown, except
-- for some imposed to zero or one by the typing rules.
data FlagValue =
    Unknown   -- ^ The value of the flag has not been decided yet.
  | One       -- ^ The value 1.
  | Zero      -- ^ The value 0.
  | Any       -- ^ Any flag value, typically the flag prefix of circ, bool, unit.
  deriving Show

-- | Information relevant to a flag. This contains the flag value, some debug
-- information used to throw detailed exceptions. Eventually, it will also contain
-- various things such as : reversability, control ..
data FlagInfo = FInfo { 
  value :: FlagValue                              -- ^ The value of the flag
}







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


-- | Removes the flag annotation from a type, returning a linear type.
-- This function doesn't make sense on typing schemes.
no_bang :: Type -> LinType
no_bang (TBang _ t) = t


-- | Checks whether a linear type uses algebraic data types.
is_user_lintype :: LinType -> Bool
is_user_lintype (TUser _ _) = True
is_user_lintype (TCirc t u) = is_user_type t || is_user_type u
is_user_lintype (TTensor tlist) = List.or $ List.map is_user_type tlist
is_user_lintype _ = False


-- | Checks whether a type uses algebraic data types.
is_user_type :: Type -> Bool
is_user_type (TBang _ a) = is_user_lintype a



-- | Specification of a user type.
data Typespec = Spec {
  args :: Int,                                             -- ^ The number of type arguments required.

  bound :: Bool,                                           -- ^ Indicates whether the type admit a finite subtree.
  qdatatype :: Bool,                                       -- ^ Is a quantum data type. Note that this flag is subject to change depending on the value of the type arguments:
                                                           -- what it says exactly is: assuming the type arguments are quantum data types, then it is a quantum data type.
                                                           -- For example, \"list a\" is a qdata type on the condition that \"a\" is itself a qdata type.

  unfolded :: ([Type], [(Datacon, Bool, Type)]),           -- ^ The unfolded defintion of the type, with on the left the type arguments, on the right the unfolded type :
                                                           -- a list of tuples (Dk, bk, Tk) where Dk is the name of the datacon, bk indicates whether the type contains any
                                                           -- algebraic types, Tk is the type of the data constructor.

  subtype :: ([Type], [Type], [TypeConstraint])            -- ^ The result of breaking the constraint {user args <: user args'}. This extension to the subtyping relation
                                                           -- is automatically inferred during the translation to the core syntax.
}



-- | Like variables (term and type), datacons are attributed unique ids.
type Datacon = Int


-- | Definition of the core patterns.
-- The definition do not differ much from that of the surface syntax, the only difference lying
-- in variables, now represented by ids.
-- Although the syntax of proto quipper doesn't make use of patterns, keeping them as syntactic sugars
-- reduces the number of variables, since the unsugaring process produces new variables, one for each
-- pair in the pattern. Some desugared code:
-- 
-- @
--    fun p -> e             ==   fun x -> let p = x in e  (and desugared again)
--
--    let \<p, q\> = e in f    ==   if p, q are variables, then it is a structure of the language
--                                  if not, the code :
--                                     let \<x, y\> = e in
--                                     let p = x in
--                                     let q = y in
--                                     e
--                                (and desugared again)
-- @
--
-- Note that the expression let x = e in f (where x is a variable), is not a syntactic sugar, as it differs from the application (fun x -> f) e by the presence
-- of let-polymorphism.
data Pattern =
    PJoker                                        -- ^ _
  | PUnit                                         -- ^ ()
  | PVar Variable                                 -- ^ x
  | PTuple [Pattern]                              -- ^ (p1, .. , pn)
  | PDatacon Datacon (Maybe Pattern)              -- ^ Datacon p
  | PLocated Pattern Extent                       -- ^ Located patterns.
  | PConstraint Pattern S.Type                    -- ^ (p <: T)
  deriving Show 


instance Located Pattern where
  location _ = Nothing
  locate p _ = p
  locate_opt p _ = p

  clear_location (PLocated p _) = clear_location p
  clear_location (PTuple plist) = PTuple $ List.map clear_location plist
  clear_location (PDatacon dcon (Just p)) = PDatacon dcon $ Just (clear_location p)
  clear_location (PConstraint p t) = PConstraint (clear_location p) t
  clear_location p = p

instance Constraint Pattern where
  drop_constraints (PConstraint p _) = drop_constraints p
  drop_constraints (PTuple plist) = PTuple $ List.map drop_constraints plist
  drop_constraints (PDatacon dcon (Just p)) = PDatacon dcon $ Just (drop_constraints p)
  drop_constraints (PLocated p ex) = PLocated (drop_constraints p) ex
  drop_constraints p = p


-- | Definition of the core expressions. The core syntax introduces global variables, imported from the dependency modules.
-- Since the global variables are suposed to be duplicable, it is not necessary to overload the typing context with
-- more variables that are duplicable anyway.
data Expr =
-- STLC
    EVar Variable                                 -- ^ x
  | EGlobal Variable                              -- ^ Global variable from the imported modules.
  | EFun Pattern Expr                             -- ^ fun p -> t
  | EApp Expr Expr                                -- ^ t u

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
  | EConstraint Expr S.Type                       -- ^ (e <: T)
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


-- | The class of objects of \'kind\' type. This includes, of course, the two LinType and Type, but also
-- everything that contains types: TypeConstraint, ConstraintSet, [TypeConstraint] ...
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


-- | Information about a constraint. Includes expression, location, orientation (on what side is the actual type).
-- It is used in type constraints and flag constraints.
data ConstraintInfo = Info {
  expression :: Expr,          -- ^ Original expression.
  loc :: Extent,          -- ^ Location of the said expression.
  actual :: Bool,              -- ^ Orientation of the constraint: true means actual to the left, false the inverse.
  in_type :: Maybe LinType -- ^ Original type (actual type before reduce).
} deriving Show


-- | Empty information.
no_info :: ConstraintInfo
no_info = Info {
  expression = EUnit,
  loc = extent_unknown,
  actual = True,
  in_type = Nothing
}



-- | The subtyping relation <: operates on both linear types and types
-- However, only constraints on types are kept, since it is the kind of constraints generated by the
-- constraint typing algorithm, and it is also useful to have the flag references at hand.
data TypeConstraint =
    Subtype Type Type ConstraintInfo              -- ^ A sub-typing constraint T <: U.
  | Sublintype LinType LinType ConstraintInfo     -- ^ A sub-typing constraint A <: B.
  deriving Show

instance Eq TypeConstraint where
  (==) (Subtype t u _) (Subtype t' u' _) = t == t' && u == u'
  (==) (Sublintype a b _) (Sublintype a' b' _) = a == a' && b == b'
  (==) _ _ = False


-- | Shortcut operator for writing sub-typing constraints.
(<:) :: Type -> Type -> TypeConstraint
t <: u = Subtype t u no_info                              


-- | Another shortcut for writing a set of constraints T1 .. Tn <: U.
(<<:) :: [Type] -> Type -> [TypeConstraint]
tlist <<: u = List.map (\t -> t <: u) tlist


-- | Another shortcut for writing a set of constraints T <: U1 .. Un.
(<::) :: Type -> [Type] -> [TypeConstraint]
t <:: ulist = List.map (\u -> t <: u) ulist


-- | Adds debug information to a set of type constraints. 
(&) :: [TypeConstraint] -> ConstraintInfo -> [TypeConstraint]
cset & info = List.map (\c -> case c of
                                Sublintype a b _ -> Sublintype a b info
                                Subtype t u _ -> Subtype t u info) cset


-- | Flag constraints, of the form n <= m, to be interpreted as
--
-- *  (n <= 0)     ==     (n :=: 0)
--
-- *  (1 <= n)     ==     (n :=: 1)
--
-- *  (m \<= n)     ==     (m = 1 =\> n = 1)
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
is_trivial (Subtype t u _) = t == u
is_trivial (Sublintype a b _) = a == b


-- | Returns true iff the constraint T <: U is atomic, meaning
-- T and U are both of the form !na where a is a type variable.
is_atomic :: TypeConstraint -> Bool
is_atomic (Sublintype (TVar _) (TVar _) _) = True
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
is_semi_composite (Sublintype t u _) =
  case (t, u) of
    (TVar _, TVar _) -> False
    (TVar _, _) -> True
    (_, TVar _) -> True
    _ -> False
is_semi_composite _ = False


-- | Returns true iff the constraint is of the form  user n a <: user n a'.
is_user :: TypeConstraint -> Bool
is_user (Sublintype t u _) =
  case (t, u) of
    (TUser _ _, TUser _ _) -> True
    _ -> False
is_user _ = False

-- | Checks whether all the constraints of a list have the same property of being right / left sided, ie:
--
-- *   of the form a <: T : left-sided
--
-- *   of the from T <: a : right-sided
--
is_one_sided :: [TypeConstraint] -> Bool
is_one_sided [] = True
is_one_sided ((Sublintype t u _):cset) =
  case (t, u) of
    (TVar _, _) -> is_left_sided cset
    (_, TVar _) -> is_right_sided cset
    _ -> False
is_one_sided _ = False


-- | Checks whether all the type constraints of a list are left sided or not.
is_left_sided :: [TypeConstraint] -> Bool
is_left_sided [] = True
is_left_sided ((Sublintype (TVar _) _ _):cset) =
  is_left_sided cset
is_left_sided _ = False


-- | Checks whether all the type constraints of a list are right sided or not.
is_right_sided :: [TypeConstraint] -> Bool
is_right_sided [] = True
is_right_sided ((Sublintype _ (TVar _) _):cset) =
  is_right_sided cset
is_right_sided _ = False


-- | Attempts to link together the input constraints, for example the set { b <: U, a <: b, T <: a } can
--  be rearranged as { T <: a <: b <: U }
--
--  The result is used in the unification algorithm: if the constraints can be linked, the approximation
--    { T \<: a \<: b \<: U }  \<=\>  a :=: b :=: T, { T \<: U } can be made
chain_constraints :: [TypeConstraint] -> (Bool, [TypeConstraint])
chain_constraints l =
  case List.find (\c -> case c of
                          Sublintype (TVar _) _ _ -> False
                          _ -> True) l of
    Just c -> case c of
                Sublintype _ (TVar y) _ -> chain_left_to_right [c] y (List.delete c l)
                _ -> error "Unreduced composite constraint"
  
    Nothing -> case List.find (\c -> case c of
                                       Sublintype _ (TVar _) _ -> False
                                       _ -> True) l of
                 Just c -> case c of
                             Sublintype (TVar y) _ _ -> chain_right_to_left [c] y (List.delete c l)
                             _ -> error "Unreduced composite constraint"
                 Nothing -> error "Only atomic constraints"



-- | Tries linking the constraints, starting from the left, and progressing by adding constraints
-- on the right.
chain_left_to_right :: [TypeConstraint] -> Int -> [TypeConstraint] -> (Bool, [TypeConstraint])
chain_left_to_right chain endvar [] = (True, List.reverse chain)
chain_left_to_right chain endvar l =
  case List.find (\c -> case c of
                          Sublintype (TVar y) _ _ -> y == endvar
                          _ -> False) l of
    Just c -> case c of
                Sublintype (TVar _) (TVar y) _ -> chain_left_to_right (c:chain) y (List.delete c l)
                _ -> if List.length l == 1 then
                       (True, List.reverse (c:chain))
                     else
                       (False, [])
    Nothing -> (False, [])


-- | Tries linking the constraints, starting from the right, and progressing by adding constraints
-- on the left.
chain_right_to_left :: [TypeConstraint] -> Int -> [TypeConstraint] -> (Bool, [TypeConstraint])
chain_right_to_left chain endvar [] = (True, chain)
chain_right_to_left chain endvar l =
  case List.find (\c -> case c of
                          Sublintype _ (TVar y) _ -> y == endvar
                          _ -> False) l of
    Just c -> case c of
                Sublintype (TVar y) (TVar _) _ -> chain_right_to_left (c:chain) y (List.delete c l)
                _ -> if List.length l == 1 then
                       (True, c:chain)
                     else
                       (False, [])
    Nothing -> (False, [])



-- | Type constraints are also of a kind ktype.
instance KType TypeConstraint where
  free_typ_var (Sublintype t u _) = List.union (free_typ_var t) (free_typ_var u)
  free_typ_var (Subtype t u _) = List.union (free_typ_var t) (free_typ_var u)
  subs_typ_var a b (Sublintype t u info) = Sublintype (subs_typ_var a b t) (subs_typ_var a b u) info
  subs_typ_var a b (Subtype t u info) = Subtype (subs_typ_var a b t) (subs_typ_var a b u) info

  free_flag (Sublintype t u _) = List.union (free_flag t) (free_flag u)
  free_flag (Subtype t u _) = List.union (free_flag t) (free_flag u)
  subs_flag n m (Sublintype t u info) = Sublintype (subs_flag n m t) (subs_flag n m u) info
  subs_flag n m (Subtype t u info) = Subtype (subs_flag n m t) (subs_flag n m u) info


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


-- | Generalizes a type, associated with constraints, over its free variables and flags.
-- The free variables of the type are those as are superior than or equal to a limit type/flag.
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


