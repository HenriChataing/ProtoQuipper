module CoreSyntax where

import Classes
import Utils
import Localizing

import Data.List as List

{-
  Definition of types :
    - Variable : to represent type variables, as well as language variables
    
    - Flag : to represent flag values. The values of flags are divided as follow :
      - 0 and 1 are reserved and are the expected value 0 and 1 (not variables)
      - -1 represent any value (0 or 1) : for example the type bool is automatically duplicable,
        so no value needs to be given to its prefix flag
      - the remaining are flag variables
-}

type Variable = Int
type Flag = Int

{-
  Definition of types
  To force the presence of flags, the definition is divided between :
  
  - LinType : 'linear types', types that are not prefixed by any annotations
 
  - Type : linear types with the addition of a prefix flag

  The division may need to be reviewed in regard of certain type constants like bool,
  unit, qbit ; flag annotation are unecessary for those constants since bool and unit
  are automatically duplicable, and qbit can never be such

  Another division would be
    - LinType : TTensor, TArrow
    - Type : TVar, TQbit, TUnit, TCirc (duplicable as well), TExp
-}

data Detail =
    ActualOfE Expr Extent      -- Meaning T is the actual type of the expression e at the extent ex
  | ActualOfP Pattern Extent   -- Meaning T is the actual type of the pattern p at the extent ex
  | NoInfo
  deriving Show

-- Select the more detailed information, with a preference for the one on the right 
more_detailed :: Detail -> Detail -> Detail
more_detailed d NoInfo = d
more_detailed _ d = d

-- Simple type
data LinSType =
    TVar Variable              -- a
  | TUser String               -- user defined type
  | TBool                      -- bool
  | TUnit                      -- 1
  | TQbit                      -- qbit
  | TTensor [Type]             -- a1 * .. * an
  | TArrow Type Type           -- a -> b
  | TCirc Type Type            -- circ (a, b)
  | TLocated LinType Extent    -- t @ ex
  deriving Show

-- Detailed type
type LinType = (LinSType, Detail)

data Type =
    TExp Flag LinType          -- !n a
  deriving Show


add_detail :: Detail -> Type -> Type
add_detail d' (TExp n (t, d)) = TExp n (t, more_detailed d' d)

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
lintype_unifier (TUnit, _) _ = (TUnit, NoInfo)
lintype_unifier _ (TUnit, _) = (TUnit, NoInfo)
lintype_unifier (TBool, _) _ = (TBool, NoInfo)
lintype_unifier _ (TBool, _) = (TBool, NoInfo)
lintype_unifier (TQbit, _) _ = (TQbit, NoInfo)
lintype_unifier _ (TQbit, _) = (TQbit, NoInfo)
lintype_unifier (TUser n, _) _ = (TUser n, NoInfo)
lintype_unifier _ (TUser n, _) = (TUser n, NoInfo)
lintype_unifier (TVar _, _) t = t
lintype_unifier t (TVar _, _) = t
lintype_unifier (TArrow t u, _) (TArrow t' u', _) = (TArrow (type_unifier t t') (type_unifier u u'), NoInfo)
lintype_unifier (TTensor tlist, _) (TTensor tlist', _) =
  case (tlist, tlist') of
    ([], []) -> (TTensor [], NoInfo)
    (t:rest, t':rest') ->
      let u = type_unifier t t'
          (TTensor urest, _) = lintype_unifier (TTensor rest, NoInfo) (TTensor rest', NoInfo) in
      (TTensor (u:urest), NoInfo)
lintype_unifier (TCirc t u, _) (TCirc t' u', _) = (TCirc (type_unifier t t') (type_unifier u u'), NoInfo)

type_unifier (TExp m t) (TExp _ u) = TExp m $ lintype_unifier t u

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

instance PPrint Flag where
  sprintn _ n | n <= 0 = ""
              | n == 1 = "!"
              | otherwise = "!" ++ (superscript $ show n)

  sprint n = sprintn defaultLvl n
  pprint n = sprintn Inf n



instance Param LinType where
  free_var (TVar x, _) = [x]
  free_var (TTensor tlist, _) = List.foldl (\fv t -> List.union (free_var t) fv) [] tlist
  free_var (TArrow t u, _) = List.union (free_var t) (free_var u)
  free_var (TCirc t u, _) = List.union (free_var t) (free_var u)
  free_var _ = []

  subs_var a b (TVar x, d) | x == a = (TVar b, d)
                        | otherwise = (TVar x, d)
  subs_var _ _ (TUnit, d) = (TUnit, d)
  subs_var _ _ (TBool, d) = (TBool, d)
  subs_var a b (TArrow t u, d) = (TArrow (subs_var a b t) (subs_var a b u), d)
  subs_var a b (TTensor tlist, d) = (TTensor $ List.map (subs_var a b) tlist, d)
  subs_var a b (TCirc t u, d) = (TCirc (subs_var a b t) (subs_var a b u), d)

instance Eq LinSType where
  (==) (TVar x) (TVar y) = x == y
  (==) TUnit TUnit = True
  (==) TBool TBool = True
  (==) TQbit TQbit = True
  (==) (TTensor tlist) (TTensor tlist') = (tlist == tlist')
  (==) (TArrow t u) (TArrow t' u') = (t == t') && (u == u')
  (==) (TCirc t u) (TCirc t' u') = (t == t') && (u == u')
  (==) _ _ = False

instance PPrint LinType where
  -- Print unto Lvl = n
  sprintn _ (TVar x, _) = subvar 'X' x
  sprintn _ (TUnit, _) = "T"
  sprintn _ (TBool, _) = "bool"
  sprintn _ (TQbit, _) = "qbit"
  sprintn _ (TUser n, _) = n
  sprintn (Nth 0) _ = "..."

  sprintn lv (TTensor (a:rest), _) =
    let dlv = decr lv in
    (case a of
       TExp _ (TArrow _ _, _) -> "(" ++ sprintn dlv a ++ ")"
       TExp _ (TTensor _, _) -> "(" ++ sprintn dlv a ++ ")"
       _ -> sprintn dlv a) ++
    List.foldl (\s b -> s ++ " * " ++
                  (case b of
                     TExp _ (TArrow _ _, _) -> "(" ++ sprintn dlv b ++ ")"
                     TExp _ (TTensor _, _) -> "(" ++ sprintn dlv b ++ ")"
                     _ -> sprintn dlv b)) "" rest

  sprintn lv (TArrow a b, _) =
    let dlv = decr lv in
    (case a of
       TExp _ (TArrow _ _, _) -> "(" ++ sprintn dlv a ++ ")"
       _ -> sprintn dlv a) ++ " -> " ++
    sprintn dlv b

  sprintn lv (TCirc a b, _) =
    let dlv = decr lv in
    "circ(" ++ sprintn dlv a ++ ", " ++ sprintn dlv b ++ ")"

  -- Print unto Lvl = +oo
  pprint a = sprintn Inf a

  -- Print unto Lvl = default
  sprint a = sprintn defaultLvl a



instance Param Type where
  free_var (TExp _ t) = free_var t
  subs_var a b (TExp n t) = TExp n (subs_var a b t)

instance Eq Type where
  (==) (TExp m (t, _)) (TExp n (t', _)) = m == n && t == t'

instance PPrint Type where
  sprintn lv (TExp f a) =
    let pf = pprint f in
    if List.length pf == 0 then
      pf ++ sprintn lv a
    else
      pf ++ (case a of
               (TTensor _, _) -> "(" ++ sprintn lv a ++ ")"
               (TArrow _ _, _) -> "(" ++ sprintn lv a ++ ")"
               _ -> sprintn lv a)
 
  -- Print unto Lvl = +oo
  pprint a = sprintn Inf a

  -- Print unto Lvl = default
  sprint a = sprintn defaultLvl a



instance Param Pattern where
  free_var PUnit = []
  free_var (PVar x) = [x]
  free_var (PData _ p) = free_var p
  free_var (PTuple plist) = List.foldl (\fv p -> List.union (free_var p) fv) [] plist
  free_var (PLocated p _) = free_var p

  subs_var _ _ p = p

instance PPrint Pattern where
   -- Print unto Lvl = n
  sprintn _ (PVar x) = subvar 'x' x
  sprintn _ PUnit = "<>"
  sprintn (Nth 0) _ = "..."

  sprintn lv (PTuple (p:rest)) =
    let dlv = decr lv in
    "<" ++ sprintn dlv p ++ List.foldl (\s q -> s ++ ", " ++ sprintn dlv q) "" rest ++ ">"

  sprintn lv (PData dcon p) =
    subvar 'D' dcon ++ "(" ++ sprintn (decr lv) p ++ ")"

  sprintn lv (PLocated p _) =
    sprintn lv p

  -- Print unto Lvl = +oo
  pprint a = sprintn Inf a

  -- Print unto Lvl = default
  sprint a = sprintn defaultLvl a



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

-- Second argument is indentation level
indent_sprintn :: Lvl -> String -> Expr -> String
------------------------------------------------
indent_sprintn _ _ EUnit = "<>"
indent_sprintn _ _ (EBool b) = if b then "true" else "false"
indent_sprintn _ _ (EVar x) = print_var x

indent_sprintn (Nth 0) _ _ = "..."

indent_sprintn lv ind (ELet p e f) =
  let dlv = decr lv in
  "let " ++ pprint p ++ " = " ++ indent_sprintn dlv ind e ++ " in\n" ++
  ind ++ indent_sprintn dlv ind f

indent_sprintn lv ind (ETuple (e:rest)) =
  let dlv = decr lv in
  "<" ++ indent_sprintn dlv ind e ++ List.foldl (\s f -> ", " ++ indent_sprintn dlv ind f) "" rest ++ ">"

indent_sprintn lv ind (EApp e f) =
  let dlv = decr lv in
  (case e of
     EFun _ _ -> "(" ++ indent_sprintn dlv ind e ++ ")"
     _ -> indent_sprintn dlv ind e) ++ " " ++
  (case f of
     EFun _ _ -> "(" ++ indent_sprintn dlv ind f ++ ")"
     EApp _ _ -> "(" ++ indent_sprintn dlv ind f ++ ")"
     _ -> indent_sprintn dlv ind f)

indent_sprintn lv ind (EFun p e) =
  let dlv = decr lv in
  "fun " ++ pprint p ++ " ->\n" ++
  ind ++ "    " ++ indent_sprintn dlv (ind ++ "    ") e

indent_sprintn lv ind (EIf e f g) =
  let dlv = decr lv in
  "if " ++ indent_sprintn dlv ind e ++ " then\n" ++
  ind ++ "  " ++ indent_sprintn dlv (ind ++ "  ") f ++ "\n" ++
  ind ++ "else\n" ++
  ind ++ "  " ++ indent_sprintn dlv (ind ++ "  ") g

indent_sprintn _ _ (EBox t) =
  "box[" ++ pprint t ++ "]"

indent_sprintn _ _ EUnbox =
  "unbox"

indent_sprintn _ _ ERev =
  "rev"

indent_sprintn lv ind (EData datacon e) =
  subvar 'D' datacon ++ "(" ++ indent_sprintn (decr lv) ind e ++ ")"

indent_sprintn lv ind (EMatch e  blist) =
  let dlv = decr lv in
  "match " ++ indent_sprintn dlv ind e ++ " with\n" ++
    List.foldl (\s (p, f) ->
                  s ++ ind ++ "  " ++ sprintn dlv p ++  " -> " ++ indent_sprintn dlv (ind ++ "  ") f ++ "\n") "" blist

indent_sprintn lv ind (ELocated e _) =
  indent_sprintn lv ind e

instance PPrint Expr where
  sprintn lv e = indent_sprintn lv "" e
  sprint e = sprintn defaultLvl e
  pprint e = sprintn Inf e

