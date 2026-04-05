;; collections/pair.cl — Pair type
;;
;; A simple two-element tuple. Used for map entries and multi-value returns.
;;
;; Spec: plan-stdlib.md §3.3

(import [prelude []])

(deftype (Pair a b) (Pair [:a first :b second]))

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
