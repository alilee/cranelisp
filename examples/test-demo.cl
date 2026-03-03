;; Testing demo: inline test module with assertions.
;;
;; Run with: just run examples/test-demo.cl
;; Or in REPL: cranelisp examples/test-demo.cl, then /run-tests

(defn add [:Int x :Int y] :Int (+ x y))
(defn double [:Int x] :Int (* x 2))

(mod test)

(defn main [] 0)
