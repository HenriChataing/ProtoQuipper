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
    TypeOfE Expr
  | TypeOfP Pattern


data LinType =
    TVar Variable              -- a
  | TBool                      -- bool
  | TUnit                      -- 1
  | TQbit                      -- qbit
  | TTensor Type Type          -- a * b
  | TSum Type Type             -- a + b
  | TArrow Type Type           -- a -> b
  | TCirc Type Type            -- circ (a, b)
  | TDetailed LinType Detail      -- Type with detailed information, as the term of which it is type

data Type =
    TExp Flag LinType          -- !n a


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

data Pattern =
    PUnit                      -- <>
  | PVar Variable              -- x
  | PPair Pattern Pattern      -- <p, q>
  deriving Show 

{-
  Definition of the expressions, nothing more to say
-}

data Expr =
    EUnit                               -- *
  | EBool Bool                          -- True / False
  | EVar Variable                       -- x
  | EFun Pattern Expr                   -- fun p -> t
  | ELet Pattern Expr Expr              -- let p = e in f
  | EApp Expr Expr                      -- t u
  | EPair Expr Expr                     -- <t, u>
  | EIf Expr Expr Expr                  -- if e then f else g
  | EInjL Expr                          -- injl e
  | EInjR Expr                          -- injr e
  | EMatch Expr (Pattern, Expr) (Pattern, Expr)
                                        -- match e with (x -> f | y -> g)
  | EBox Type                           -- box[T]
  | EUnbox Expr                         -- unbox t
  | ERev                                -- rev
  | ELocated Expr Extent                -- e @ ex

{-
   Remove the addtional information of a linear type
-}
undetailed :: LinType -> LinType
--------------------------------
undetailed (TDetailed t _) = t
undetailed t = t

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
lintype_unifier (TVar _) t = t
lintype_unifier t (TVar _) = t
lintype_unifier (TArrow t u) (TArrow t' u') = TArrow (type_unifier t t') (type_unifier u u')
lintype_unifier (TTensor t u) (TTensor t' u') = TTensor (type_unifier t t') (type_unifier u u')
lintype_unifier (TSum t u) (TSum t' u') = TSum (type_unifier t t') (type_unifier u u')
lintype_unifier (TCirc t u) (TCirc t' u') = TCirc (type_unifier t t') (type_unifier u u')
lintype_unifier (TDetailed t _) t' = lintype_unifier t t'
lintype_unifier t (TDetailed t' _) = lintype_unifier t t'

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
  free_var (TVar x) = [x]
  free_var (TTensor t u) = List.union (free_var t) (free_var u)
  free_var (TArrow t u) = List.union (free_var t) (free_var u)
  free_var (TSum t u) = List.union (free_var t) (free_var u)
  free_var (TCirc t u) = List.union (free_var t) (free_var u)
  free_var (TDetailed t _) = free_var t
  free_var _ = []

  subs_var a b (TVar x) | x == a = TVar b
                        | otherwise = TVar x
  subs_var _ _ TUnit = TUnit
  subs_var _ _ TBool = TBool
  subs_var a b (TArrow t u) = TArrow (subs_var a b t) (subs_var a b u)
  subs_var a b (TSum t u) = TSum (subs_var a b t) (subs_var a b u) 
  subs_var a b (TTensor t u) = TTensor (subs_var a b t) (subs_var a b u)
  subs_var a b (TCirc t u) = TCirc (subs_var a b t) (subs_var a b u)
  subs_var a b (TDetailed t d) = TDetailed (subs_var a b t) d

instance Eq LinType where
  (==) (TVar x) (TVar y) = x == y
  (==) TUnit TUnit = True
  (==) TBool TBool = True
  (==) TQbit TQbit = True
  (==) (TTensor t u) (TTensor t' u') = (t == t') && (u == u')
  (==) (TArrow t u) (TArrow t' u') = (t == t') && (u == u')
  (==) (TSum t u) (TSum t' u') = (t == t') && (u == u')
  (==) (TCirc t u) (TCirc t' u') = (t == t') && (u == u')
  (==) (TDetailed t _) t' = t == t'
  (==) t (TDetailed t' _) = t == t'
  (==) _ _ = False

instance PPrint LinType where
  -- Print unto Lvl = n
  sprintn _ (TVar x) = subscript ("X" ++ show x)
  sprintn _ TUnit = "T"
  sprintn _ TBool = "bool"
  sprintn _ TQbit = "qbit"
  sprintn (Nth 0) _ = "..."

  sprintn lv (TTensor a b) =
    let dlv = decr lv in
    (case a of
       TExp _ (TArrow _ _) -> "(" ++ sprintn dlv a ++ ")"
       TExp _ (TTensor _ _) -> "(" ++ sprintn dlv a ++ ")"
       _ -> sprintn dlv a) ++ " * " ++
    (case b of
       TExp _ (TArrow _ _) -> "(" ++ sprintn dlv b ++ ")"
       TExp _ (TTensor _ _) -> "(" ++ sprintn dlv b ++ ")"
       _ -> sprintn dlv b)

  sprintn lv (TArrow a b) =
    let dlv = decr lv in
    (case a of
       TExp _ (TArrow _ _) -> "(" ++ sprintn dlv a ++ ")"
       _ -> sprintn dlv a) ++ " -> " ++
    sprintn dlv b

  sprintn lv (TSum a b) =
    let dlv = decr lv in
    (case a of
       TExp _ (TSum _ _) -> "(" ++ sprintn dlv a ++ ")"
       _ -> sprintn dlv a) ++ " + " ++
    sprintn dlv b

  sprintn lv (TCirc a b) =
    let dlv = decr lv in
    "circ(" ++ sprintn dlv a ++ ", " ++ sprintn dlv b ++ ")"

  sprintn lv (TDetailed t _) =
    sprintn lv t

  -- Print unto Lvl = +oo
  pprint a = sprintn Inf a

  -- Print unto Lvl = default
  sprint a = sprintn defaultLvl a



instance Param Type where
  free_var (TExp _ t) = free_var t
  subs_var a b (TExp n t) = TExp n (subs_var a b t)

instance Eq Type where
  (==) (TExp m t) (TExp n t') = m == n && t == t'

instance PPrint Type where
  sprintn lv (TExp f a) =
    let pf = pprint f in
    if List.length pf == 0 then
      pf ++ sprintn lv a
    else
      pf ++ (case a of
               TTensor _ _ -> "(" ++ sprintn lv a ++ ")"
               TArrow _ _ -> "(" ++ sprintn lv a ++ ")"
               _ -> sprintn lv a)
 
  -- Print unto Lvl = +oo
  pprint a = sprintn Inf a

  -- Print unto Lvl = default
  sprint a = sprintn defaultLvl a



instance Param Pattern where
  free_var PUnit = []
  free_var (PVar x) = [x]
  free_var (PPair p q) = List.union (free_var p) (free_var q)

  subs_var _ _ p = p

instance PPrint Pattern where
   -- Print unto Lvl = n
  sprintn _ (PVar x) = subscript ("x" ++ show x)
  sprintn _ PUnit = "<>"
  sprintn (Nth 0) _ = "..."

  sprintn lv (PPair a b) =
    let dlv = decr lv in
    "<" ++ sprintn dlv a ++ ", " ++ sprintn dlv b ++ ">"

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

  free_var (EPair e f) =
    List.union (free_var e) (free_var f)

  free_var (EIf e f g) =
    List.union (List.union (free_var e) (free_var f)) (free_var g)

  free_var (EInjL e) = free_var e
  free_var (EInjR e) = free_var e

  free_var (EMatch e (p, f) (q, g)) =
    let fve = free_var e
        fvf = free_var f
        fvg = free_var g
        fvp = free_var p
        fvq = free_var q in
    List.union fve (List.union (fvf \\ fvp) (fvg \\ fvq))

  free_var (EUnbox t) =
    free_var t
  
  free_var _ =
    []

  subs_var _ _ e = e

print_var x = subscript ("x" ++ show x)

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

indent_sprintn lv ind (EPair e f) =
  "<" ++ indent_sprintn (decr lv) ind e ++ ", " ++ indent_sprintn (decr lv) ind f ++ ">"

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

indent_sprintn lv ind (EUnbox t) =
  "unbox (" ++ indent_sprintn (decr lv) ind t ++ ")"

indent_sprintn _ _ ERev =
  "rev"

indent_sprintn lv ind (EInjL e) =
  "injl(" ++ indent_sprintn (decr lv) ind e ++ ")"

indent_sprintn lv  ind (EInjR e) =
  "injr(" ++ indent_sprintn (decr lv) ind e ++ ")"

indent_sprintn lv ind (EMatch e (p, f) (q, g)) =
  let dlv = decr lv in
  "match " ++ indent_sprintn dlv ind e ++ " with\n" ++
  ind ++ "  | " ++ pprint p ++ " -> " ++ indent_sprintn dlv (ind ++ "    ") f ++ "\n" ++
  ind ++ "  | " ++ pprint q ++ " -> " ++ indent_sprintn dlv (ind ++ "    ") g

instance PPrint Expr where
  sprintn lv e = indent_sprintn lv "" e
  sprint e = sprintn defaultLvl e
  pprint e = sprintn Inf e

