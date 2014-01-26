" Vim syntax file
" Language Proto-Quipper
" Maintainer Henri Chataing
" Latest Revision 15 August 2013

if exists("b:current_syntax")
  finish
endif

syn match number '\d\+'
syn match basicOps '<-\|<-\*\|->\|=\|;\|:\||'
syn match basicOps '[- < > | & $ @ + * / % . : =]\+'
syn match variable '[a-zA-Z_]\w*'
syn match circuitOps 'box\s*\[.*\]'
syn region commented start='--' end='$'
syn region commented start='{-' end='-}'
syn match printable contained '[^ "]'
syn match string '"[^"]*"'

syn keyword header type of import and
syn keyword circuitOps unbox rev
syn keyword basicOps let rec in fun match with if then else
syn keyword constants true false

let b:current_syntax = "prquipper"

hi def link number        Constant
hi def link string        Constant
hi def link constants     Constant
hi def link commented     Comment
hi def link header        PreProc
hi def link basicOps      Statement
hi def link circuitOps    Type
