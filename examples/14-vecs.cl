;; 14-vecs.cl -- Vec: growable arrays
;;
;; Vec is a heap-allocated growable array type. Elements are stored
;; contiguously in memory for fast indexed access.
;;
;; Creating a Vec:
;;   [1 2 3]         ;; Vec literal with 3 elements
;;   []              ;; Empty Vec
;;
;; Vec primitives:
;;   (vec-len v)       ;; Number of elements
;;   (vec-get v i)     ;; Get element at index i (0-based, bounds-checked)
;;   (vec-set v i x)   ;; Return new Vec with element i replaced by x
;;   (vec-push v x)    ;; Return new Vec with x appended
;;
;; Vec is polymorphic: [1 2 3] has type (Vec Int),
;; ["a" "b"] has type (Vec String), etc.
;;
;; vec-set and vec-push use copy-on-write: if the Vec has only one
;; reference, mutation happens in-place for efficiency.
;;
;; The vec primitives are also ordinary VALUES: they can be passed to
;; higher-order functions like any user-defined function (see the
;; "Vec operations as ordinary values" section below).
;;
;; Expected exit code: 81 — the process exit status is a single byte, so
;; the sum of sub-test results (593) is reported as its low byte,
;; 593 mod 256 = 81. (Several earlier examples wrap the same way; 05 is
;; the first.)

;; --- Basic operations ---

;; Create and measure
(defn check-literal []
  (vec-len [10 20 30 40 50]))

;; Access elements by index
(defn check-get []
  (let [v [10 20 30]]
    (add-i64 (vec-get v 0)
             (add-i64 (vec-get v 1)
                      (vec-get v 2)))))

;; Replace an element
(defn check-set []
  (vec-get (vec-set [10 20 30] 1 99) 1))

;; Append an element
(defn check-push []
  (let [v (vec-push [1 2] 3)]
    (add-i64 (vec-len v) (vec-get v 2))))

;; --- Building Vecs incrementally ---

;; Start empty and push elements
(defn check-from-empty []
  (vec-len (vec-push (vec-push (vec-push [] 1) 2) 3)))

;; Chain multiple sets
(defn check-set-chain []
  (let [v (vec-set (vec-set (vec-set [0 0 0] 0 1) 1 2) 2 3)]
    (add-i64 (vec-get v 0)
             (add-i64 (vec-get v 1)
                      (vec-get v 2)))))

;; --- Vecs as function arguments ---

(defn sum-first-two [v]
  (add-i64 (vec-get v 0) (vec-get v 1)))

(defn check-as-arg []
  (sum-first-two [100 200 300]))

;; --- Vec operations as ordinary values ---

;; The vec primitives are first-class: a name like `vec-get` is an
;; ordinary function value, so it can be passed to a higher-order
;; function just like a user-defined one (higher-order functions are
;; example 13's capability).
;;
;; `apply2` below is one generic helper, and it is used at two different
;; vec primitives: `vec-get` (index in, element out) and `vec-push`
;; (element in, Vec out). Each call site instantiates it at that
;; primitive's own type.

(defn apply2 [f v x] (f v x))
(defn apply3 [f v i x] (f v i x))

;; Pass vec-get itself as the argument: (vec-get [7 8 9] 1) = 8
(defn check-get-as-value []
  (apply2 vec-get [7 8 9] 1))

;; Pass vec-set: replace index 0 with 40, then read it back.
(defn check-set-as-value []
  (vec-get (apply3 vec-set [1 2 3] 0 40) 0))

;; Pass vec-push: append a fourth element, then measure.
(defn check-push-as-value []
  (vec-len (apply2 vec-push [1 2 3] 4)))

;; --- Vecs in ADTs ---

(deftype (Pair a b) (MkPair [:a fst :b snd]))

(defn check-vec-in-adt []
  (match (MkPair [10 20] 42)
    [(MkPair v n) (add-i64 (vec-get v 1) n)]))

;; --- Summing results ---

;; Expected: 5 + 60 + 99 + 6 + 3 + 6 + 300 + 62 + 8 + 40 + 4 = 593
;; Exit code is the low byte of main's return: 593 mod 256 = 81.
(defn main []
  ;; Wrap the sum-of-pass-counts in `Pure`: every batch `main` must
  ;; return `IO _`. The inner Int is the exit code (preserved).
  (Pure
    (add-i64 (check-literal)
      (add-i64 (check-get)
        (add-i64 (check-set)
          (add-i64 (check-push)
            (add-i64 (check-from-empty)
              (add-i64 (check-set-chain)
                (add-i64 (check-as-arg)
                  (add-i64 (check-vec-in-adt)
                    (add-i64 (check-get-as-value)
                      (add-i64 (check-set-as-value)
                               (check-push-as-value)))))))))))))
