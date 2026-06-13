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

;; --- Basic operations ---

;; Create and measure
(defn test-literal []
  (vec-len [10 20 30 40 50]))

;; Access elements by index
(defn test-get []
  (let [v [10 20 30]]
    (add-i64 (vec-get v 0)
             (add-i64 (vec-get v 1)
                      (vec-get v 2)))))

;; Replace an element
(defn test-set []
  (vec-get (vec-set [10 20 30] 1 99) 1))

;; Append an element
(defn test-push []
  (let [v (vec-push [1 2] 3)]
    (add-i64 (vec-len v) (vec-get v 2))))

;; --- Building Vecs incrementally ---

;; Start empty and push elements
(defn test-from-empty []
  (vec-len (vec-push (vec-push (vec-push [] 1) 2) 3)))

;; Chain multiple sets
(defn test-set-chain []
  (let [v (vec-set (vec-set (vec-set [0 0 0] 0 1) 1 2) 2 3)]
    (add-i64 (vec-get v 0)
             (add-i64 (vec-get v 1)
                      (vec-get v 2)))))

;; --- Vecs as function arguments ---

(defn sum-first-two [v]
  (add-i64 (vec-get v 0) (vec-get v 1)))

(defn test-as-arg []
  (sum-first-two [100 200 300]))

;; --- Vecs in ADTs ---

(deftype (Pair a b) (MkPair [:a fst :b snd]))

(defn test-vec-in-adt []
  (match (MkPair [10 20] 42)
    [(MkPair v n) (add-i64 (vec-get v 1) n)]))

;; --- Summing results ---

;; Expected: 5 + 60 + 99 + 6 + 3 + 6 + 300 + 62 = 541
(defn main []
  ;; Wrap the sum-of-pass-counts in `Pure`: every batch `main` must
  ;; return `IO _`. The inner Int is the exit code (preserved).
  (Pure
    (add-i64 (test-literal)
      (add-i64 (test-get)
        (add-i64 (test-set)
          (add-i64 (test-push)
            (add-i64 (test-from-empty)
              (add-i64 (test-set-chain)
                (add-i64 (test-as-arg)
                         (test-vec-in-adt))))))))))
