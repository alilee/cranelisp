;; L-B1 golden-CLIF corpus 04 — vec COW loop (vec-push growth, vec-set
;; copy-on-write, vec-get/vec-len reads — all DIRECT calls; vec-op value-use
;; shapes are corpus-EXCLUDED per ../EXCLUSIONS.md). Free-standing; green by
;; construction. This is the borrow-elision/stack-slot mechanisms' primary
;; reshape surface (biggest expected B3.2 re-baseline).
(import [primitives [*]])

(defn build [v :Int i :Int n]
  (if (eq-i64 i n) v
    (build (vec-push v i) (add-i64 i 1) n)))

(defn sum [v :Int i :Int n :Int acc]
  (if (eq-i64 i n) acc
    (sum v (add-i64 i 1) n (add-i64 acc (vec-get v i)))))

(defn main []
  (let [v (build [] 0 16)
        w (vec-set v 0 100)]
    (Pure (add-i64 (sum v 0 (vec-len v) 0) (vec-get w 0)))))
