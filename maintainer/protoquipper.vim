" Vim syntax file
" Language Proto-Quipper
" Maintainer Henri Chataing
" Latest Revision 15 August 2013

if exists("b:current_syntax")
  finish
endif

syn match qNumber '\d\+'
syn region circuitOps start='box' end='\]'
syn match commented '-- .*$'
syn match basicOps '|'
syn match header '#builtin [A-Z a-z '_' 0-9]*'

syn keyword header type of import
syn keyword circuitOps unbox rev
syn keyword basicOps let rec in fun match with if then else
syn keyword constants true false

let b:current_syntax = "prquipper"

hi def link number        Constant
hi def link constants     Constant
hi def link commented     Comment
hi def link header        PreProc
hi def link basicOps      Statement
hi def link circuitOps    Type
hi def link bracketType   Statement
