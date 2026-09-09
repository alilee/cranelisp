;; 33-definition-ordering.cl -- Forward references in one compilation cluster
;;
;; A file's non-macro definitions form one compilation cluster. Functions,
;; types, traits, and implementations can refer to one another before their
;; definitions appear in the source. This lets you arrange a program around
;; its callers, with the helpers below them.
;;
;; Each function name has one defn in the cluster. Writing a second defn
;; for the same name rejects the cluster; it does not replace the first:
;;
;;   (defn step [x] (add-i64 x 1))
;;   (defn step [x] (mul-i64 x 3))  ;; Illegal together in one file.
;;
;; Live replacement happens across separate REPL inputs, after the earlier
;; definition has been committed. Source order inside a file is different:
;; all the calls below use the one definition of each name.
;;
;; Expected exit code: 6, one per passing check.

;; --- A caller before its helper ---

;; step need not have appeared yet for twice to use it.
(defn twice [x] (step (step x)))
(defn step [x] (mul-i64 x 3))

(defn test-direct []
  (if (eq-i64 (step 2) 6) 1 0))

(defn test-forward-call []
  (if (eq-i64 (twice 2) 18) 1 0))

;; --- Forward references through a dependency chain ---

;; Both links point forward: top calls mid, and mid calls base.
(defn top [] (add-i64 (mid) 100))
(defn mid [] (add-i64 (base) 10))
(defn base [] 2)

(defn test-forward-chain []
  (if (eq-i64 (top) 112) 1 0))

;; --- Callers before a trait implementation ---

;; The traits and product types from examples 15 and 20 participate in
;; the same cluster. These callers can use size before its Box impl.
(deftrait Sized
  (size [x] Int))

(deftype Box [:Int n])

(defn boxed-size [b] (size b))
(defn twice-boxed-size [b] (add-i64 (boxed-size b) (boxed-size b)))

(impl Sized Box
  (defn size [b] (match b [(Box v) (mul-i64 v 10)])))

(defn test-impl-direct []
  (if (eq-i64 (size (Box 5)) 50) 1 0))

(defn test-impl-forward-call []
  (if (eq-i64 (boxed-size (Box 5)) 50) 1 0))

(defn test-impl-forward-chain []
  (if (eq-i64 (twice-boxed-size (Box 5)) 100) 1 0))

;; main returns the six pass counts in IO, using Pure as in example 21.
(defn main []
  (Pure
    (add-i64 (test-direct)
      (add-i64 (test-forward-call)
        (add-i64 (test-forward-chain)
          (add-i64 (test-impl-direct)
            (add-i64 (test-impl-forward-call)
                     (test-impl-forward-chain))))))))
