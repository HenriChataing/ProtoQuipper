{- This module contains the conversion from the pattern-less proto quipper to Continuation Passing Style. -}
module Compiler.CPS where

import Prelude hiding (lookup)

import Utils
import Classes hiding ((<+>))

import Monad.QpState
import Monad.QuipperError

import qualified Compiler.SimplSyntax as S
import Compiler.Circ
import Compiler.Interfaces

import qualified Data.List as List
import Text.PrettyPrint.HughesPJ as PP



-- | The definition of values.
data Value =
    VVar Variable          -- ^ A variable.
  | VInt Int               -- ^ An integer.
  | VLabel Variable        -- ^ A function label.
  | VBuiltin Variable      -- ^ A builtin operation. The Qlib and Builtins module don't necessarily write their functions in closure closed-form,
                           -- so they need to be identified so as to treat the function calls accordingly.
  deriving (Show, Eq)


instance Param Value where
  free_var (VVar x) = [x]
  free_var (VLabel x) = [x]
  free_var (VBuiltin x) = [x]
  free_var _ = []

  subs_var _ _ v = v



-- | Definition of continuations.
data CExpr =
    CFun Variable [Variable] CExpr CExpr           -- ^ Function abstraction: @fun x1 .. xN -> t@.
  | CApp Value [Value]                             -- ^ Function application: @t u@.
  | CTuple [Value] Variable CExpr                  -- ^ Tuple: @(/t/1, .. , /t//n/)@. By construction, must have /n/ >= 2.
  | CAccess Int Value Variable CExpr               -- ^ Access the nth element of a tuple.
  | CSwitch Value [CExpr]                          -- ^ Switch condition.
  deriving Show



instance Param CExpr where
  free_var (CFun f args cf c) =
    List.union (free_var cf List.\\ args) (free_var c)
  free_var (CApp f args) =
    List.foldl (\fv a ->
          List.union (free_var a) fv) (free_var f) args
  free_var (CTuple vlist x c) =
    let fvl = List.foldl (\fv a ->
          List.union (free_var a) fv) [] vlist in
    List.union (free_var c List.\\ [x]) fvl
  free_var (CAccess _ v x c) =
    List.union (free_var c List.\\ [x]) (free_var v)
  free_var (CSwitch v clist) =
    List.foldl (\fv c ->
          List.union (free_var c) fv) (free_var v) clist

  subs_var _ _ c = c



-- | Replace a variable by a value into a continuation expression.
replace :: Variable -> Value -> CExpr -> CExpr
replace x v (CFun f arg e e') =
  CFun f arg (replace x v e) (replace x v e')
replace x v (CApp f arg) =
  let f' = rep_val x v f
      arg' = List.map (rep_val x v) arg in
  CApp f' arg'
replace x v (CTuple vlist y e) =
  let vlist' = List.map (rep_val x v) vlist in
  CTuple vlist' y (replace x v e)
replace x v (CAccess n w y e) =
  CAccess n (rep_val x v w) y (replace x v e)
replace x v (CSwitch w elist) =
  CSwitch (rep_val x v w) (List.map (replace x v) elist)

-- | Application of the function replace to a single value.
rep_val x v (VVar y) | x == y = v
                     | otherwise = VVar y
rep_val _ _ v = v


-- | Convert an expression from the simplified syntax to the continuation passing style.
convert_to_cps :: (IQLib, IBuiltins)              -- ^ Interfaces to the QLib and Builtins modules.
               -> (Value -> QpState CExpr)        -- ^ A continuation.
               -> S.Expr                          -- ^ Argument expression.
               -> QpState CExpr                   -- ^ The resulting continuation expression.

convert_to_cps dict c (S.EVar v) =
  c (VVar v)

convert_to_cps dict c (S.EGlobal v) =
  c (VVar v)

convert_to_cps dict c (S.EInt n) =
  c (VInt n)

convert_to_cps dict c (S.EBool b) =
  c (if b then VInt 1 else VInt 0)

convert_to_cps dict c S.EUnit =
  c (VInt 0)

convert_to_cps dict c (S.ETuple []) =
  c (VInt 0)

convert_to_cps dict c (S.ETuple elist) = do
  x <- create_var "x"
  aux elist (\w -> do
        cx <- c (VVar x)
        return $ CTuple w x cx)
  where
    aux l c = do
      let aux' [] w = c (List.reverse w)
          aux' (e:es) w = convert_to_cps dict (\v -> aux' es (v:w)) e
      aux' l []

convert_to_cps dict c (S.EAccess n x) = do
  y <- create_var "x"
  cy <- c (VVar y)
  return $ CAccess n (VVar x) y cy
  
convert_to_cps dict c (S.EFun x e) = do
  f <- create_var "x"       -- function name
  k <- create_var "x"       -- continuation argument
  -- At the end of the body, the result is passed to the continuation k
  body <- convert_to_cps dict (\z -> return $ CApp (VVar k) [z]) e 
  -- The reference f of the function is passed to the building continuation c
  cf <- c (VVar f)
  return $ CFun f [x, k] body $ cf

convert_to_cps dict c (S.ERecFun f x e) = do
  k <- create_var "x"       -- continuation argument
  -- At the end of the body, the result is passed to the continuation k
  body <- convert_to_cps dict (\z -> return $ CApp (VVar k) [z]) e 
  -- The reference f of the function is passed to the building continuation c
  cf <- c (VVar f)
  return $ CFun f [x, k] body $ cf

convert_to_cps dict c (S.EApp e f) = do
  r <- create_var "x"       -- return address
  x <- create_var "x"       -- argument of the return address
  app <- convert_to_cps dict (\f -> convert_to_cps dict (\e -> return $ CApp f [e, VVar r]) e) f
  cx <- c (VVar x)
  return $ CFun r [x] cx app

convert_to_cps dict c (S.ESeq e f) = do
  convert_to_cps dict (\z -> convert_to_cps dict c f) e

convert_to_cps dict c (S.ELet x e f) = do
  convert_to_cps dict (\z -> do
        cf <- convert_to_cps dict c f
        return $ replace x z cf) e

convert_to_cps dict c (S.EIf e f g) = do
  k <- create_var "x"
  x <- create_var "x"
  cx <- c (VVar x)
  f' <- convert_to_cps dict (\z -> return $ CApp (VVar k) [z]) f
  g' <- convert_to_cps dict (\z -> return $ CApp (VVar k) [z]) g
  convert_to_cps dict (\e ->
        return $ CFun k [x] cx $
                 CSwitch e [g', f']) e

convert_to_cps dict c (S.EMatch e blist) = do
  k <- create_var "x"
  x <- create_var "x"
  cx <- c (VVar x)
  let slist = List.sortBy (\(n,_) (m,_) -> compare n m) blist
  elist' <- List.foldl (\rec (_, e) -> do
        es <- rec
        e' <- convert_to_cps dict (\z -> return $ CApp (VVar k) [z]) e
        return $ e':es) (return []) slist
  convert_to_cps dict (\e ->
        return $ CFun k [x] cx $
                 CSwitch e (List.reverse elist')) e

convert_to_cps (iqlib, ibuiltins) c (S.EBuiltin s) =
  case lookup s iqlib of
    Just v -> c (VBuiltin v)
    Nothing ->
        case lookup s ibuiltins of
          Just v -> c (VBuiltin v)
          Nothing -> fail $ "CPS:convert_to_cps: undefined builtin operation: " ++ s





-- | Convert the toplevel declarations into the CPS form.
-- By default, the evalution finishes by a call to @exit 0@.
convert_declarations :: (IQLib, IBuiltins)         -- ^ Interfaces to the QLib and Builtins modules.
                     -> [S.Declaration]            -- ^ List of declarations.
                     -> QpState CExpr              -- ^ Resulting continuationj expression.
convert_declarations dict decls = do
  let vexit = case lookup "EXIT" (snd dict) of
        Just v -> VBuiltin v
        Nothing -> throwNE $ ProgramError "CPS:convert_declarations: undefined builtin operation: EXIT"

  List.foldr (\d rec -> do
        ce <- rec
        case d of
          S.DExpr e -> do
              convert_to_cps dict (\_ -> return ce) e
          
          S.DLet x e -> do
              r <- create_var "x"
              convert_to_cps dict (\z ->
                    return $ CFun r [x] ce $
                             CApp (VVar r) [z]) e
    ) (return $ CApp vexit [VInt 0]) decls


-- | Closure conversion of the CPS code.
closure_conversion :: CExpr -> QpState CExpr
closure_conversion (CFun f args cf c) = do
  -- close the function body and continuation
  cf' <- closure_conversion cf
  c' <- closure_conversion c

  -- free variables of f
  let fv = free_var cf'
  -- name of the function pointer and closure
  f' <- create_var "f"
  f'' <- create_var "f"
  cl <- create_var "c"

  -- extraction of the free variables of cf'
  let cf'' = List.foldl (\cf (x,n) ->
        CAccess n (VVar f'') x cf) cf' $ List.zip fv [1..List.length fv]

  -- construction of the closure (with continuation c' and name f)
  let c'' = CTuple (VVar f':(List.map VVar fv)) f c'

  -- re-definition of the function f
  return $ CFun f' (f'':args) cf'' c''

closure_conversion (CApp (VVar f) args) = do
  f' <- create_var "f"
  return $ CAccess 0 (VVar f) f' $                     -- Extract the function pointer
           CApp (VLabel f') (VVar f:args)              -- Apply the function to its own closure
  
closure_conversion (CTuple clist x c) = do
  c' <- closure_conversion c
  return $ CTuple clist x c

closure_conversion (CAccess n v x c) = do
  c' <- closure_conversion c
  return $ CAccess n v x c'

closure_conversion (CSwitch v clist) = do
  clist' <- List.foldl (\rec c -> do
        cl <- rec
        c' <- closure_conversion c
        return $ c':cl) (return []) clist
  return $ CSwitch v (List.reverse clist')

closure_conversion c =
  return c


-- | Lift the function definitions to the top of the module.
-- This function separates the function definitions from the rest of the continuation expression.
-- Since this operation is sound only if the functions are closed, this has to be done after the closure conversion.
lift_functions :: CExpr -> ([(Variable, [Variable], CExpr)],CExpr)
lift_functions (CFun f args cf c) =
  let (funs, c') = lift_functions c
      (funs', cf') = lift_functions cf in
  ((f,args,cf'):(funs' ++ funs), c')

lift_functions (CTuple vlist x c) =
  let (funs, c') = lift_functions c in
  (funs, CTuple vlist x c')

lift_functions (CAccess n x y c) =
  let (funs, c') = lift_functions c in
  (funs, CAccess n x y c')

lift_functions (CSwitch v clist) =
  let (funs, clist') = List.foldl (\(fs, cl) c ->
        let (fs', c') = lift_functions c in
        (fs' ++ fs, c':cl)) ([], []) clist in
  (funs, CSwitch v $ List.reverse clist')

lift_functions c =
 ([], c)



-- | Pretty-print a value using Hughes's and Peyton Jones's
-- pretty printer combinators. The type 'Doc' is defined in the library
-- "Text.PrettyPrint.HughesPJ" and allows for nested documents.
print_value :: (Variable -> String)  -- ^ Rendering of term variables.
            -> Value                 -- ^ Expression to print.
            -> Doc                   -- ^ Resulting PP document.
print_value _ (VInt n) =
  text (show n)
print_value fvar (VVar v) =
  text (fvar v)
print_value fvar (VBuiltin v) =
  text (fvar v)
print_value fvar (VLabel v) =
  text (fvar v)


-- | Pretty-print an expression using Hughes's and Peyton Jones's
-- pretty printer combinators. The type 'Doc' is defined in the library
-- "Text.PrettyPrint.HughesPJ" and allows for nested documents.
print_cfun :: (Variable -> String)                      -- ^ Rendering of term variables.
           -> (Variable, [Variable], CExpr)             -- ^ Function to print.
           -> Doc                                       -- ^ Resulting PP document.
print_cfun fvar (f, [], cf) =
  text (fvar f ++ "() {") $$
  nest 2 (print_cexpr Inf fvar cf) $$
  text "}"
print_cfun fvar (f, args, cf) =
  let pargs = List.map (text . fvar) args
      sargs = punctuate comma (List.init pargs) ++ [List.last pargs] in
  text (fvar f ++ "(") <> hsep sargs <> text ") {" $$
  nest 2 (print_cexpr Inf fvar cf) $$
  text "}"


-- | Pretty-print a continuation function using Hughes's and Peyton Jones's
-- pretty printer combinators. The type 'Doc' is defined in the library
-- "Text.PrettyPrint.HughesPJ" and allows for nested documents.
print_cexpr :: Lvl                   -- ^ Maximum depth.
            -> (Variable -> String)  -- ^ Rendering of term variables.
            -> CExpr                 -- ^ Expression to print.
            -> Doc                   -- ^ Resulting PP document.
print_cexpr _ fvar (CApp f []) =
  text (show f) <+> text "();"
print_cexpr _ fvar (CApp f args) =
  let pargs = List.map (print_value fvar) args
      sargs = punctuate comma pargs in
  print_value fvar f <> text "(" <> hsep sargs <> text ");"
print_cexpr _ fvar (CTuple vals x c) =
  let pvals = List.map (print_value fvar) vals
      svals = punctuate comma pvals in
  text (fvar x ++ " := [") <> hsep svals <> text "];" $$
  print_cexpr Inf fvar c
print_cexpr _ fvar (CAccess n x y c) =
  text (fvar y ++ " :=") <+> print_value fvar x <> text ("[" ++ show n ++ "];") $$
  print_cexpr Inf fvar c
print_cexpr _ fvar (CSwitch v clist) =
  let tags = [0 .. List.length clist-1]
      pcs = List.map (print_cexpr Inf fvar) clist in
  text "switch" <+> print_value fvar v <+> text "with" $$
  nest 2 (List.foldl (\doc (tag, c) ->
        doc $$
        text (show tag ++ ":") $$
        nest 2 c) (text "") (List.zip tags pcs))
print_cexpr _ fvar (CFun _ _ _ _) =
  text ""



-- | Printing of expressions. The function 'genprint' generalizes the display of term
-- variables and data constructors.
instance PPrint CExpr where
  -- Generic printing
  genprint lv [fvar] e =
    let doc = print_cexpr lv fvar e in
    PP.render doc
  genprint lv _ e =
    throwNE $ ProgramError "Preliminaries:genprint(CExpr): illegal argument"

  -- Other
  -- By default, the term variables are printed as x_n and the data constructors as D_n,
  -- where n is the id of the variable / constructor
  sprintn lv e = genprint lv [prevar "%"] e



-- | Print the CPS code, after lifting of the function declarations.
print_CPS :: (Variable -> String) -> ([(Variable, [Variable], CExpr)], CExpr) -> String
print_CPS fvar (cfuns, c) =
  let pcfuns = List.map (print_cfun fvar) cfuns
      pc = print_cexpr Inf fvar c in

  let all = List.foldl (\doc cfun -> cfun $$ doc) pc pcfuns in
  PP.render all

