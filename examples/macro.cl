(platform stdio)
(import [platform.stdio [*]])

; Example: compile-time macros
;
; defmacro defines a function (SList Sexp) -> Sexp that transforms
; S-expressions before type checking.

; A simple macro that wraps an expression in (+ expr 1)
(defmacro my-inc [x]
  (SexpList (slist (SexpSym "+") x (SexpInt 1))))

; A macro that generates an if expression
(defmacro my-when [cond body]
  (SexpList (slist (SexpSym "if") cond body (SexpInt 0))))

(defn main []
  (do
    (print (show (my-inc 41)))
    (print "\n")
    (print (show (my-when true 42)))
    (print "\n")
    (pure 0)))
