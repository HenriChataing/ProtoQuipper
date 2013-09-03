;; An Emacs editing mode for Proto-Quipper

;; This should be loaded with (load "proto-quipper-mode.el") in your
;; .emacs file.

(setq proto-quipper-myKeywords
 '(("\\b\\(and\\|box\\|false\\|rev\\|unbox\\|true\\|#builtin\\)\\b" . font-lock-constant-face)
   ("\\b\\(bool\\|circ\\|int\\|qubit\\|list\\)\\b" . font-lock-type-face)
   ("^\\(let\\|rec\\|type\\|val\\|import\\)\\b" . font-lock-function-name-face)
   (";;" . font-lock-function-name-face)
   ("\\b\\(let\\|else\\|fun\\|if\\|in\\|match\\|of\\|then\\|with\\)\\b" . font-lock-keyword-face)
   ("[-=.<>+]" . font-lock-keyword-face)
  )
)

;; syntax table
(defvar proto-quipper-syntax-table nil "Syntax table for `proto-quipper-mode'.")
(setq proto-quipper-syntax-table
      (let ((synTable (make-syntax-table)))

	;; Haskell-style comment "-- ..." 
	;; (modify-syntax-entry ?- ". 12b" synTable)

	;; Haskell-style comment "{- ... -}"
	(modify-syntax-entry ?\{ "(}1nb" synTable)
	(modify-syntax-entry ?\} "){4nb" synTable)
	(modify-syntax-entry ?- "_ 123" synTable)
	(modify-syntax-entry ?\n ">" synTable)

	(modify-syntax-entry ?_ "w")
	(modify-syntax-entry ?# "w")

        synTable))


(define-derived-mode proto-quipper-mode fundamental-mode
  "proto-quipper-mode is a major mode for editing Proto-Quipper."
  :syntax-table proto-quipper-syntax-table

  (setq font-lock-defaults '(proto-quipper-myKeywords))
  (setq mode-name "Proto-Quipper")
)

(setq auto-mode-alist (cons '(".*\\.qp$" . proto-quipper-mode)
                        auto-mode-alist))

(provide 'proto-quipper-mode)
