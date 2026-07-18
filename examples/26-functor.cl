;; 26-functor.cl -- Higher-kinded types with Functor trait
;;
;; Higher-kinded types (HKT) let traits abstract over type constructors
;; rather than concrete types. A regular trait like Eq abstracts over
;; types of kind * (e.g., Int, Bool). A higher-kinded trait like
;; Functor abstracts over type constructors of kind * -> * (e.g.,
;; Option, List).
;;
;; The Functor trait defines fmap -- applying a function to the value(s)
;; inside a container while preserving the container's structure:
;;
;;   (deftrait (Functor f)
;;     (fmap [:(Fn [a] b) func :(f a) x] (f b)))
;;
;; HKT method params are named with explicit annotations (spec §7.2.2):
;; func is the function (a -> b), x is the container (f a).
;; The (f a) and (f b) in the signature mean "f applied to a" and
;; "f applied to b". When f = Option, fmap transforms the value
;; inside a Some and passes None through unchanged.
;;
;; Prior examples used traits parameterized over concrete types (Num,
;; Eq, Ord, Display). This example introduces a trait parameterized
;; over a type constructor.

;; --- The Option type (from example 10) ---

(deftype (Option a) None (Some [:a val]))

(defn unwrap-or [opt default]
  (match opt
    [(Some x) x
     None     default]))

;; --- The Functor trait: higher-kinded ---

;; (Functor f) says: f is a type constructor (kind * -> *).
;; fmap takes a function (a -> b) and a container (f a),
;; and returns a new container (f b) with the function applied.
(deftrait (Functor f)
  (fmap [:(Fn [a] b) func :(f a) x] (f b)))

;; --- Implement Functor for Option ---

;; When fmap is called on (Option a), it pattern-matches:
;;   Some x  =>  Some (f x)   -- apply the function
;;   None    =>  None          -- nothing to transform
;;
;; An impl of a higher-kinded trait ECHOES the trait's declared head in
;; slot 1 -- `(Functor f)`, the same `(Functor f)` written in the deftrait,
;; con-var spelling and all -- and names a trait-constructor pairing in
;; slot 2: `(Functor Option)`, the trait applied to the bare constructor
;; being implemented. (Conventional kind-* traits keep the bare-head form,
;; e.g. `(impl Display Int ...)`; only higher-kinded traits echo the head.)
(impl (Functor f) (Functor Option)
  (defn fmap [f opt]
    (match opt
      [None    None
       (Some x) (Some (f x))])))

;; --- Helper functions ---

(defn inc [x] (add-i64 x 1))
(defn double [x] (mul-i64 x 2))

;; --- Tests ---

;; fmap over Some: applies the function to the contained value
(defn test-fmap-some []
  (unwrap-or (fmap inc (Some 41)) 0))                     ;; -> 42

;; fmap over None: returns None unchanged
(defn test-fmap-none []
  (unwrap-or (fmap inc None) 99))                          ;; -> 99

;; fmap double over Some
(defn test-fmap-double []
  (unwrap-or (fmap double (Some 21)) 0))                   ;; -> 42

;; Chaining fmap: apply two transformations in sequence
(defn test-fmap-chain []
  (unwrap-or (fmap double (fmap inc (Some 10))) 0))        ;; -> 22

;; Chaining fmap over None: both fmaps are no-ops
(defn test-fmap-chain-none []
  (unwrap-or (fmap double (fmap inc None)) 99))            ;; -> 99

;; fmap with a closure that captures context
(defn test-fmap-closure []
  (let [offset 40]
    (unwrap-or (fmap (fn [x] (add-i64 x offset)) (Some 2)) 0)))  ;; -> 42

;; fmap preserves None through any function
(defn test-fmap-preserves-none []
  (if (match (fmap double None) [None true _ false]) 1 0))       ;; -> 1

;; Expected: 42 + 99 + 42 + 22 + 99 + 42 + 1 = 347
(defn main []
  ;; Wrap the sum-of-pass-counts in `Pure`: every batch `main` must
  ;; return `IO _`. The inner Int is the exit code (preserved).
  (Pure
    (add-i64 (test-fmap-some)
      (add-i64 (test-fmap-none)
        (add-i64 (test-fmap-double)
          (add-i64 (test-fmap-chain)
            (add-i64 (test-fmap-chain-none)
              (add-i64 (test-fmap-closure)
                       (test-fmap-preserves-none)))))))))
