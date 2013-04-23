module Lexer where

import Data.Char
import PMonad

data Token =
    TokenEmpty
  | TokenVar String
  | TokenFun
  | TokenCirc
  | TokenEq
  | TokenArrow
  | TokenTrue
  | TokenFalse
  | TokenLet
  | TokenIn
  | TokenIf
  | TokenThen
  | TokenElse
  | TokenLBracket
  | TokenRBracket
  | TokenComma
  | TokenBox
  | TokenUnbox
  | TokenLParen
  | TokenRParen
  | TokenLBrace
  | TokenRBrace
  | TokenRev
  | TokenBool
  | TokenQBit
  | TokenBang
  | TokenEOF
    deriving Show

lexer :: (Token -> P a) -> P a
lexer cont s =
  case s of
    [] ->  cont TokenEOF []
    ('\n':cs) -> \(l, c) -> lexer cont cs (l+1, c)
    ('*':cs) -> \(l, c) -> cont TokenEmpty cs (l, c+1)
    (',':cs) -> \(l, c) -> cont TokenComma cs (l, c+1)
    ('=':cs) -> \(l, c) -> cont TokenEq cs (l, c+1)
    ('!':cs) -> \(l, c) -> cont TokenBang cs (l, c+1)
    ('(':cs) -> \(l, c) -> cont TokenLParen cs (l, c+1)
    (')':cs) -> \(l, c) -> cont TokenRParen cs (l, c+1)
    ('<':cs) -> \(l, c) -> cont TokenLBracket cs (l, c+1)
    ('>':cs) -> \(l, c) -> cont TokenRBracket cs (l, c+1)
    ('[':cs) -> \(l, c) -> cont TokenLBrace cs (l, c+1)
    (']':cs) -> \(l, c) -> cont TokenRBrace cs (l, c+1)
    ('-':'>':cs) -> \(l, c) -> cont TokenArrow cs (l, c+2)
    (ch:cs) -> if isSpace ch then
		\(l, c) -> lexer cont cs (l, c+1)
              else if isAlpha ch then
                lexVar cont (ch:cs)
              else
           	\(l, c) -> Failed ("Lexing error -- At point " ++ show l ++ ":" ++ show c ++" - Unkown character " ++ [ch])

lexVar :: (Token -> P a) -> P a
lexVar cont cs =
  case span isAlpha cs of
  ("True", rest) -> \(l, c) -> cont TokenTrue rest (l, c+4)
  ("False", rest) -> \(l, c) -> cont TokenFalse rest (l, c+5)
  ("fun", rest) -> \(l, c) -> cont TokenFun rest (l, c+3)
  ("box", rest) -> \(l, c) -> cont TokenBox rest (l, c+3)
  ("circ", rest) -> \(l, c) -> cont TokenCirc rest (l, c+4)
  ("unbox", rest) -> \(l, c) -> cont TokenUnbox rest (l, c+5)
  ("rev", rest) -> \(l, c) -> cont TokenRev rest (l, c+3)
  ("bool", rest) -> \(l, c) -> cont TokenBool rest (l, c+4)
  ("qbit", rest) -> \(l, c) -> cont TokenQBit rest (l, c+4)
  ("let", rest) -> \(l, c) -> cont TokenLet rest (l, c+3)
  ("in", rest) -> \(l, c) -> cont TokenIn rest (l, c+2)
  ("if", rest) -> \(l, c) -> cont TokenIf rest (l, c+2)
  ("then", rest) -> \(l, c) -> cont TokenThen rest (l, c+4)
  ("else", rest) -> \(l, c) -> cont TokenElse rest (l, c+4)
  (var, rest) -> \(l, c) -> cont (TokenVar var) rest (l, c+length var)

