(import [primitives [*]])

;; ── Functor Trait ───────────────────────────────────

(deftrait (Functor f) "Mappable container"
  (fmap "Apply function to values inside container" [(Fn [a] b) (f a)] (f b)))

;; ── List Type ───────────────────────────────────────

(deftype (List a) "A singly-linked immutable list"
  (Nil "The empty list")
  (Cons "A list node with head element and tail" [:a head :(List a) tail]))

;; ── List Operations ─────────────────────────────────

(defn empty? "Returns true if list is empty" [xs]
  (match xs
    [Nil true
     _ false]))

(defn concat "Concatenate two lists" [xs ys]
  (match xs
    [Nil ys
     (Cons h t) (Cons h (concat t ys))]))

(defn list-reduce "Reduce a list with function and initial accumulator" [f init xs]
  (match xs
    [Nil init
     (Cons h t) (list-reduce f (f init h) t)]))

(impl Functor List
  (defn fmap [f lst]
    (match lst
      [Nil Nil
       (Cons h t) (Cons (f h) (fmap f t))])))

(defn reverse "Reverse a list" [xs]
  (list-reduce (fn [acc x] (Cons x acc)) Nil xs))
