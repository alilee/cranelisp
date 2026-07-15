;; collections/pair.cl — Pair type
;;
;; A simple two-element tuple. Used for map entries and multi-value returns.
;;
;; `Pair` is seeded by `primitives` (it is part of the return type of
;; `discover-tests :: ... (Vec (Pair String (Fn [] (Option String))))`).
;; To keep ONE canonical `Pair` type across the system, this module
;; RE-EXPORTS the primitives `Pair` rather than defining a second, distinct
;; ADT — mirroring `fn.option`. The combinators below operate over the SAME
;; `primitives/Pair` type.
;;
;; Spec: plan-stdlib.md §3.3, 08-modules.md §8.6.4

(import [prelude []])
(import [primitives [Pair]])
(export [primitives [Pair]])

(defn first "Extract the first element of a pair" [p]
  (match p
    [(Pair a _) a]))

(defn second "Extract the second element of a pair" [p]
  (match p
    [(Pair _ b) b]))

(defn map-first "Apply function to the first element" [f p]
  (match p
    [(Pair a b) (Pair (f a) b)]))

(defn map-second "Apply function to the second element" [f p]
  (match p
    [(Pair a b) (Pair a (f b))]))

(defn swap "Swap the elements of a pair" [p]
  (match p
    [(Pair a b) (Pair b a)]))

;; ── Self-tests ───────────────────────────────────────────────────────
;; `(mod- test …)` submodule (S87 Stage C.2): exercises the pair accessors
;; with the in-language harness.

(mod- test)  ;; body in pair/test.cl (extraction-stable backing file, spec §8.2.5)
