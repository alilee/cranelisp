(platform stdio)
(import [platform.stdio [*]])

;; Reader shortcuts: quote, auto-gensym, anonymous functions

;; Quote — build Sexp values with '
(defn show-quote []
  (do
    (print "--- Quote ---")
    (print (show (match 'foo
      [(SexpSym name) name
       _ "?"])))
    (print (show (match '42
      [(SexpInt n) n
       _ 0])))
    (print (show (match '(+ 1 2)
      [(SexpList _) "got-list"
       _ "?"])))))

;; Auto-gensym — hygienic macros with x#
(defmacro my-let1 [v b] `(let [x# ~v] (+ x# ~b)))

(defn show-gensym []
  (do
    (print "--- Gensym ---")
    (print (show (my-let1 10 5)))
    (print (show (let [x 100] (+ (my-let1 10 5) x))))))

;; Anonymous function — #(...)
(defn show-anon-fn []
  (do
    (print "--- Anon Fn ---")
    (print (show (#(+ % 1) 5)))
    (print (show (#(* %1 %2) 3 4)))
    (print (show (#(+ %1 %2) 10 20)))))

(defn main []
  (do
    (show-quote)
    (show-gensym)
    (show-anon-fn)))
