;;; test-table-mode --- Test Table Mode

;;; Commentary:

;;; Code:

(require 'rx)

;;COMMENT      : "/*" .*? "*/" -> channel(HIDDEN);



(setq -test-table-mode-font-lock
      (let* ((keywords '("relational" "table" "options"
                         ">>" "_p"
                         "var" "state" "input" "output" "group" "row" "pause" "as"
                         "of" "omega" "gvar" "with"
                         "FUNCTION" "END_FUNCTION"
                         "function" "end_function"
                         "if" "fi"))
             (seperators '("," ":" ";"))
             (operators '("=" "[" "]" "->" "&" "AND" "=>" "/"
                          "=" ">=" ">" "[" "<=" "<"
                          "-" "%"  "MOD" "*" "!"  "NOT" "<>" "!="
                          "|" "OR" "+" "**" "XOR" "xor" "::"))
             (bconstant '("TRUE" "FALSE" "false" "true"))
             (keywords-re (regexp-opt keywords 'words))
             (bconstant-re (regexp-opt bconstant 'words))
             (operators-re (regexp-opt operators 'words))
             (seperators-re (regexp-opt seperators 'words))
             (number-re (rx (+ (any num) (? "." (any num)) (? (any "eE") (any num)))))
             (line-comment-re (rx "//" (* nonl) eol)))

        (let* ((identifier-plain
                '(: (any letter) (* (any alnum "$"))))
               (identifier-relational
                `(: (* (any alnum))
                    (| "|>" "·")
                    (? ,identifier-plain)))
               (identifier-re
                (rx-to-string `(| ,identifier-plain  ,identifier-relational)))
               (identifier-esacpes-re
                (rx bos "`" (* nonl) "`" eos)))
          `((,line-comment-re . font-lock-comment-face)
            (,identifier-esacpes-re . font-lock-function-name-face)
            (,keywords-re . font-lock-keyword-face)
            (,number-re . font-lock-constant-face)
            (,bconstant-re . font-lock-constant-face)
            (,operators-re . font-lock-builtin-face)
            (,seperators-re . font-lock-builtin-face)
            (,identifier-re . font-lock-function-name-face)
            ))))


;;COMMENT      : "/*" .*? "*/" -> channel(HIDDEN);

(defvar test-table-mode-map nil "")
(progn
  (setq test-table-mode-map (make-sparse-keymap))
  (define-key test-table-mode-map (kbd "C-c C-a") #'(lambda () (message "test"))))

;;"{" "}"
;;"(" ")"


(defvar test-table-mode-syntax-table nil "")
(setq test-table-mode-syntax-table
      (let ((table (make-syntax-table)))
        ;; ' is a string delimiter
        (modify-syntax-entry ?' "\"" table)
        ;; " is a string delimiter too
        (modify-syntax-entry ?\" "\"" table)
        (modify-syntax-entry ?` "w" table)


        ;; / is punctuation, but // is a comment starter
        (modify-syntax-entry ?/ ". 12" table)
        ;; \n is a comment ender
        (modify-syntax-entry ?\n ">" table)
        table))



;;###autoload

(define-derived-mode test-table-mode prog-mode
  "Test Table"
  "A simple mode for writing relational and generalized test table.
   KeyMap \\{test-table-mode-map}"
  :syntax-table test-table-mode-syntax-table

  (setq-local comment-start "/*")
  (setq-local comment-end "*)")
  (setq-local font-lock-defaults '(-test-table-mode-font-lock nil nil)) ;set CASE-FOLD t
  (message "test-table-mode executed")
  )

(add-to-list 'auto-mode-alist  '(".tt.txt\\'" . test-table-mode))


(provide 'test-table-mode)

;;; test-table-mode ends here
