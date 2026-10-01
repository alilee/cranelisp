;; 26-functor.cl -- Higher-kinded types with Functor trait
;;
;; Higher-kinded types (HKT) let traits abstract over type constructors
;; rather than concrete types. A regular trait like Eq abstracts over
;; types of kind * (e.g., Int, Bool). A higher-kinded trait like
;; Functor abstracts over type constructors of kind * -> * (e.g.,
;; Option, IO).
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

;; IO and bind come from example 21; the IO instance near the end uses them.
(import [primitives [IO bind]])

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
(defn check-fmap-some []
  (unwrap-or (fmap inc (Some 41)) 0))                     ;; -> 42

;; fmap over None: returns None unchanged
(defn check-fmap-none []
  (unwrap-or (fmap inc None) 99))                          ;; -> 99

;; fmap double over Some
(defn check-fmap-double []
  (unwrap-or (fmap double (Some 21)) 0))                   ;; -> 42

;; Chaining fmap: apply two transformations in sequence
(defn check-fmap-chain []
  (unwrap-or (fmap double (fmap inc (Some 10))) 0))        ;; -> 22

;; Chaining fmap over None: both fmaps are no-ops
(defn check-fmap-chain-none []
  (unwrap-or (fmap double (fmap inc None)) 99))            ;; -> 99

;; fmap with a closure that captures context
(defn check-fmap-closure []
  (let [offset 40]
    (unwrap-or (fmap (fn [x] (add-i64 x offset)) (Some 2)) 0)))  ;; -> 42

;; fmap preserves None through any function
(defn check-fmap-preserves-none []
  (if (match (fmap double None) [None true _ false]) 1 0))       ;; -> 1

;; --- Implement Functor for IO ---

;; A Functor need not be a container. IO is a type constructor too:
;; `(IO a)` describes an effect that yields an `a`. fmap over IO
;; transforms the value the effect will yield and runs nothing itself.
;; This is example 21's `map-io`, written as an instance.
(impl (Functor f) (Functor IO)
  (defn fmap [f io]
    (bind io (fn [x] (Pure (f x))))))

;; fmap over IO: the functions apply to the value the action yields
(defn check-fmap-io []
  (fmap double (fmap inc (Pure 20))))                      ;; -> (IO 42)

;; Expected: 42 + 99 + 42 + 22 + 99 + 42 + 1 + 42 = 389
;; The process EXIT CODE is the low byte of that sum: 389 mod 256 = 133.
(defn main []
  ;; check-fmap-io is an IO action, so main binds its result before
  ;; adding it to the pure checks and wrapping the sum in `Pure`.
  (bind (check-fmap-io)
    (fn [io-result]
      (Pure
        (add-i64 io-result
          (add-i64 (check-fmap-some)
            (add-i64 (check-fmap-none)
              (add-i64 (check-fmap-double)
                (add-i64 (check-fmap-chain)
                  (add-i64 (check-fmap-chain-none)
                    (add-i64 (check-fmap-closure)
                             (check-fmap-preserves-none))))))))))))
