;; collections/either.cl — Either type
;;
;; A generic two-way sum type. Left and Right carry values of different types.
;; Used when a function can produce one of two unrelated result types.
;;
;; Spec: plan-stdlib.md §3.3

(import [prelude []])

(deftype (Either a b) (Left [:a val]) (Right [:b val]))

(defn is-left? "Test if an Either is Left" [e]
  (match e
    [(Left _) true
     (Right _) false]))

(defn is-right? "Test if an Either is Right" [e]
  (match e
    [(Left _) false
     (Right _) true]))

(defn from-left "Extract Left value or return default" [default e]
  (match e
    [(Left v) v
     (Right _) default]))

(defn from-right "Extract Right value or return default" [default e]
  (match e
    [(Left _) default
     (Right v) v]))

(defn map-left "Apply function to Left value, pass through Right" [f e]
  (match e
    [(Left v) (Left (f v))
     (Right v) (Right v)]))

(defn map-right "Apply function to Right value, pass through Left" [f e]
  (match e
    [(Left v) (Left v)
     (Right v) (Right (f v))]))

(defn either "Eliminate an Either: apply f to Left or g to Right" [f g e]
  (match e
    [(Left v) (f v)
     (Right v) (g v)]))
