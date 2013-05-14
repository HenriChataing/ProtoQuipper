module TransCore where

import CoreSyntax
import qualified Syntax as S

import Contexts
import Localizing

import Data.Map

--------------------------------------
-- Translation into internal Syntax --

-- Translation of types
translateType :: S.Type -> Context -> (FType, Context)
-------------------------------------------
translateType (S.TLocated t _) ctx = translateType t ctx

translateType S.TUnit ctx =
  let (f, ctx0) = freshFlag ctx in
  (FTyp TUnit f, ctx0)

translateType S.TBool ctx =
  let (f, ctx0) = freshFlag ctx in
  (FTyp TBool f, ctx0)

translateType S.TQBit ctx =
  let (f, ctx0) = freshFlag ctx in
  (FTyp TQBit f, ctx0 { fConstraints = (FIs f 0):(fConstraints ctx0) }) -- A qbit type can never be banged

translateType (S.TExp t) ctx =
  let (ft@(FTyp t' f), ctx1) = translateType (S.stripExp t) ctx in
  (ft, ctx1 { fConstraints = (FIs f 1):(fConstraints ctx1) })           -- Since the type was originally banged, the flag is on

translateType (S.TCirc t1 t2) ctx =
  let (ft1, ctx1) = translateType t1 ctx in
  let (ft2, ctx2) = translateType t2 ctx1 in
  let (f, ctx3) = freshFlag ctx2 in
  (FTyp (TCirc ft1 ft2) f, ctx3)

translateType (S.TTensor t1 t2) ctx =
  let (ft1, ctx1) = translateType t1 ctx in
  let (ft2, ctx2) = translateType t2 ctx1 in
  let (f, ctx3) = freshFlag ctx2 in
  (FTyp (TTensor ft1 ft2) f, ctx3)

translateType (S.TArrow t1 t2) ctx =
  let (ft1, ctx1) = translateType t1 ctx in
  let (ft2, ctx2) = translateType t2 ctx1 in
  let (f, ctx3) = freshFlag ctx2 in
  (FTyp (TArrow ft1 ft2) f, ctx3)


-- Translation of patterns
translatePattern :: S.Pattern -> Context -> (Pattern, Context)
--------------------------------------------------------------
translatePattern (S.PLocated p ex) ctx = translatePattern p (ctx { extent = ex })
translatePattern S.PUnit ctx = (PUnit, ctx)
translatePattern (S.PVar v) ctx =
  let (uid, ctx0) = register v ctx in
  (PVar (Var { uid = uid, ext = extent ctx0 }), ctx0) 
translatePattern (S.PPair p1 p2) ctx =
  let (cp1, ctx1) = translatePattern p1 ctx in
  let (cp2, ctx2) = translatePattern p2 ctx1 in
  (PPair cp1 cp2, ctx2)
translatePattern (S.PConstraint p t) ctx =
  let (cp, ctx0) = translatePattern p ctx in
  let (ft, ctx1) = translateType t ctx0 in
  (PConstraint cp ft, ctx1)


-- Translation of expressions
translateExpr :: S.Expr -> Context -> (Expr, Context)
-----------------------------------------------------
translateExpr (S.ELocated e ex) ctx =
  let (ce, ctx0) = translateExpr e ctx in
  (ELocated ce ex, ctx0)

translateExpr S.EUnit ctx = (EUnit, ctx)

translateExpr (S.EConstraint e t) ctx =
  let (ce, ctx0) = translateExpr e ctx in
  let (ft, ctx1) = translateType t ctx in
  (EConstraint ce ft, ctx1)

translateExpr S.ERev ctx = (ERev, ctx)

translateExpr (S.EBox t) ctx =
  let (ft, ctx0) = translateType t ctx in
  (EBox ft, ctx0)

translateExpr (S.EBool b) ctx = (EBool b, ctx)

translateExpr (S.EUnbox e) ctx =
  let (ce, ctx0) = translateExpr e ctx in
  (EUnbox ce, ctx)

translateExpr (S.EVar v) ctx =
  case Data.Map.lookup v $ fromName ctx of
  Just uid ->
      -- Normal case : the name has been defined
      (EVar (Var { uid = uid, ext = extent ctx }), ctx)
  Nothing ->
      -- No name registered : unbound variable
      error ("Unbound variable " ++ v ++ ", at extent " ++ (show $ extent ctx))

translateExpr (S.EFun p e) ctx =
  let (cp, ctx0) = translatePattern p ctx in
  let (ce, ctx1) = translateExpr e ctx0 in
  (EFun cp ce, ctx1 { fromName = fromName ctx } )  -- Note : drop all bindings issued inside the function

translateExpr (S.ELet p e1 e2) ctx =
  let (ce1, ctx0) = translateExpr e1 ctx in
  let (cp, ctx1) = translatePattern p ctx0 in
  let (ce2, ctx2) = translateExpr e2 ctx1 in
  (ELet cp ce1 ce2, ctx2 { fromName = fromName ctx } ) -- Note : drop all bindings issued inside the let expression

translateExpr (S.EApp e1 e2) ctx =
  let (ce1, ctx1) = translateExpr e1 ctx in
  let (ce2, ctx2) = translateExpr e2 ctx1 in
  (EApp ce1 ce2, ctx2)
translateExpr (S.EPair e1 e2) ctx =
  let (ce1, ctx1) = translateExpr e1 ctx in
  let (ce2, ctx2) = translateExpr e2 ctx1 in
  (EPair ce1 ce2, ctx2)
translateExpr (S.EIf e1 e2 e3) ctx =
  let (ce1, ctx1) = translateExpr e1 ctx in
  let (ce2, ctx2) = translateExpr e2 ctx1 in
  let (ce3, ctx3) = translateExpr e3 ctx2 in
  (EIf ce1 ce2 ce3, ctx3)

