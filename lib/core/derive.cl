(mod numerics)
(mod formats)
(mod syntax)
(import [primitives [*] macros [*] numerics [*] formats [*] syntax [*]])

;; ── Layer 1: SList utilities ───────────────────────────

(defn- slength "Count elements in an SList" [xs]
  (sfold (fn [acc _] (+ acc 1)) 0 xs))

(defn- snth "Get nth element of an SList (0-indexed)" [:Int n xs]
  (match xs
    [SNil (SexpSym "error-snth-out-of-bounds")
     (SCons h t) (if (= n 0) h (snth (- n 1) t))]))

(defn- smap "Map a function over an SList" [f xs]
  (sreverse (sfold (fn [acc x] (SCons (f x) acc)) SNil xs)))

(defn- sdrop "Drop first n elements from an SList" [:Int n xs]
  (if (= n 0) xs
    (match xs
      [SNil SNil
       (SCons _ t) (sdrop (- n 1) t)])))

;; ── Layer 1: Deftype introspection ─────────────────────

(defn- dt-head "Get the name-part sexp (second element)" [dt]
  (match dt
    [(SexpList items)
     (match items
       [(SCons _ tail1)
        (match tail1
          [(SCons head _) head
           _ (SexpSym "error-dt-head")])
        _ (SexpSym "error-dt-head")])
     _ (SexpSym "error-dt-head")]))

(defn- dt-has-docstring "Check if deftype has a docstring after name" [dt]
  (let [third (sdrop 2 (match dt [(SexpList items) items _ SNil]))]
    (match third
      [(SCons elem _)
       (match elem
         [(SexpStr _) true
          _ false])
       _ false])))

(defn- dt-name "Extract type name string from deftype sexp" [dt]
  (let [head (dt-head dt)]
    (match head
      [(SexpSym s) s
       (SexpList items)
       (match items
         [(SCons first _)
          (match first [(SexpSym s) s _ "error-dt-name"])
          _ "error-dt-name"])
       _ "error-dt-name"])))

(defn- dt-params "Extract type param names as SList of Strings" [dt]
  (let [head (dt-head dt)]
    (match head
      [(SexpSym _) SNil
       (SexpList items)
       (match items
         [(SCons _ params) (smap (fn [p] (match p [(SexpSym s) s _ "error"])) params)
          _ SNil])
       _ SNil])))

(defn- dt-body "Get constructor sexps after name and optional docstring" [dt]
  (match dt
    [(SexpList items)
     (match items
       [(SCons _ tail1)
        (match tail1
          [(SCons _ rest)
           (if (dt-has-docstring dt)
             (match rest [(SCons _ ctors) ctors _ SNil])
             rest)
           _ SNil])
        _ SNil])
     _ SNil]))

(defn- dt-constructors "Get constructor sexps as SList" [dt]
  (let [body (dt-body dt)]
    (match body
      [(SCons first _)
       (match first
         [(SexpBracket _)
          (SCons (SexpList (SCons $((dt-name dt)) body)) SNil)
          _ body])
       _ SNil])))

(defn- ctor-name "Extract constructor name string" [ctor]
  (match ctor
    [(SexpSym s) s
     (SexpList items)
     (match items
       [(SCons first _)
        (match first [(SexpSym s) s _ "error-ctor-name"])
        _ "error-ctor-name"])
     _ "error-ctor-name"]))

(defn- ctor-nullary? "Check if constructor has no fields" [ctor]
  (match ctor
    [(SexpSym _) true
     _ false]))

(defn- ctor-fields-raw "Get raw field items from bracket in data constructor" [ctor]
  (match ctor
    [(SexpList items)
     (match items
       [(SCons _ tail1)
        (match tail1
          [(SCons bracket-sexp _)
           (match bracket-sexp
             [(SexpBracket fields) fields
              _ SNil])
           _ SNil])
        _ SNil])
     _ SNil]))

(defn- ctor-field-count "Count fields in a constructor" [ctor]
  (if (ctor-nullary? ctor)
    0
    (/ (slength (ctor-fields-raw ctor)) 2)))

;; ── Layer 2: Sexp building helpers ─────────────────────

(defn- make-binding "Generate a single binding name like __da3" [:String prefix :Int i]
  (SexpSym (str-concat prefix (int-to-string i))))

(defn- make-bindings-acc "Accumulator helper for make-bindings" [:String prefix :Int n :Int i acc]
  (if (= i n) acc
    (make-bindings-acc prefix n (+ i 1) (SCons (make-binding prefix i) acc))))

(defn- make-bindings "Generate __prefix0, __prefix1, ... as SList of SexpSym" [:String prefix :Int n]
  (sreverse (make-bindings-acc prefix n 0 SNil)))

;; TCO helper: zip two SLists into reversed list of pairs
(defn- szip-rev-acc "Zip two SLists into reversed list of (a b) pairs" [xs ys acc]
  (match xs
    [SNil acc
     (SCons x xt)
     (match ys
       [(SCons y yt) (szip-rev-acc xt yt (SCons (SCons x (SCons y SNil)) acc))
        _ acc])]))

(defn- build-eq-chain "Build (if (= a0 b0) (if (= a1 b1) ... true) false) from two SLists" [as bs]
  (let [rev-pairs (szip-rev-acc as bs SNil)]
    (sfold (fn [inner pair]
      (match pair
        [(SCons a rest)
         (match rest
           [(SCons b _) `(if (= ~a ~b) ~inner false)
            _ inner])
         _ inner]))
      `true
      rev-pairs)))

(defn- build-eq-nullary-arm "Build match arm pair for nullary ctor in Eq" [ctor]
  (let [s $((ctor-name ctor))]
    (SCons s (SCons `(match b [~s true _ false]) SNil))))

(defn- build-eq-data-arm "Build match arm pair for data ctor in Eq" [ctor]
  (let [name (ctor-name ctor)
        n (ctor-field-count ctor)
        abinds (make-bindings "__da" n)
        bbinds (make-bindings "__db" n)
        outer-pat (SexpList (SCons $name abinds))
        inner-pat (SexpList (SCons $name bbinds))
        field-eq (build-eq-chain abinds bbinds)]
    (SCons outer-pat (SCons `(match b [~inner-pat ~field-eq _ false]) SNil))))

(defn- build-eq-arms "Build all match arm pairs for Eq" [ctors]
  (sfold (fn [acc ctor]
    (sconcat acc
      (if (ctor-nullary? ctor)
        (build-eq-nullary-arm ctor)
        (build-eq-data-arm ctor))))
    SNil ctors))

;; ── Polymorphic constraint propagation ─────────────────

(defn- ctor-field-types-acc "Extract type sexps from field pairs" [items acc]
  (match items
    [SNil acc
     (SCons type-sexp rest)
     (match rest
       [SNil acc
        (SCons _ rest2) (ctor-field-types-acc rest2 (SCons type-sexp acc))])]))

(defn- ctor-field-types "Get field type annotation sexps from a data ctor" [ctor]
  (sreverse (ctor-field-types-acc (ctor-fields-raw ctor) SNil)))

(defn- scontains? "Check if an SList of Strings contains a given String" [:String needle haystack]
  (match haystack
    [SNil false
     (SCons h t) (if (= h needle) true (scontains? needle t))]))

(defn- dt-constraints-for-trait "Collect type params that need trait constraint" [:String trait-name params dt]
  (let [ctors (dt-constructors dt)
        param-strs (smap (fn [p] (str-concat ":" p)) params)]
    (sfold (fn [acc ctor]
      (if (ctor-nullary? ctor) acc
        (let [types (ctor-field-types ctor)]
          (sfold (fn [acc2 type-sexp]
            (match type-sexp
              [(SexpSym s)
               (if (scontains? s param-strs)
                 (if (scontains? s acc2) acc2
                   (SCons s acc2))
                 acc2)
               _ acc2]))
            acc types))))
      SNil ctors)))

(defn- build-impl-target "Build impl target sexp with constraints" [:String name params :String trait-name dt]
  (if (sempty? params)
    $name
    (let [constrained (dt-constraints-for-trait trait-name params dt)
          param-sexps (smap (fn [p]
            (let [colon-p (str-concat ":" p)]
              (if (scontains? colon-p constrained)
                (slist $((str-concat ":" trait-name)) $p)
                (slist $p))))
            params)]
      (SexpList (SCons $name (sfold sconcat SNil param-sexps))))))

;; ── Layer 3: derive-Eq macro ───────────────────────────

(defmacro derive-Eq "Derive Eq trait implementation" [dt]
  `(impl Eq ~(build-impl-target (dt-name dt) (dt-params dt) "Eq" dt)
     (defn = [a b] (match a ~(SexpBracket (build-eq-arms (dt-constructors dt)))))))

;; ── Ord helpers ────────────────────────────────────────

(defn- build-later-arms "Build SList of (name true) pairs for later constructors" [all-names :Int len :Int j lacc]
  (if (= j len) lacc
    (build-later-arms all-names len (+ j 1)
      (sconcat lacc (SCons (snth j all-names) (SCons `true SNil))))))

(defn- build-ord-enum-lt-go "Accumulator for building enum < arms" [all-names :Int len remaining :Int idx acc]
  (match remaining
    [SNil acc
     (SCons ctor rest)
     (let [name-sym $((ctor-name ctor))
           later (build-later-arms all-names len (+ idx 1) SNil)
           inner-arms (sconcat later (SCons (SexpSym "_") (SCons `false SNil)))
           arm-pair (SCons name-sym (SCons `(match b ~(SexpBracket inner-arms)) SNil))]
       (build-ord-enum-lt-go all-names len rest (+ idx 1) (sconcat acc arm-pair)))]))

(defn- build-ord-enum-lt-arms "Build < arms for enum: each ctor is less than later ones" [ctors]
  (let [all-names (smap (fn [c] $((ctor-name c))) ctors)
        len (slength all-names)]
    (build-ord-enum-lt-go all-names len ctors 0 SNil)))

(defn- build-ord-lexico-chain "Build lexicographic < comparison from two binding lists" [as bs]
  (let [rev-pairs (szip-rev-acc as bs SNil)]
    (sfold (fn [inner pair]
      (match pair
        [(SCons a rest)
         (match rest
           [(SCons b _) `(if (< ~a ~b) true (if (= ~a ~b) ~inner false))
            _ inner])
         _ inner]))
      `false
      rev-pairs)))

(defn- build-ord-data-lt-arms "Build < arms for data ctor with fields" [ctor]
  (let [name (ctor-name ctor)
        n (ctor-field-count ctor)
        abinds (make-bindings "__da" n)
        bbinds (make-bindings "__db" n)
        outer-pat (SexpList (SCons $name abinds))
        inner-pat (SexpList (SCons $name bbinds))
        field-lt (build-ord-lexico-chain abinds bbinds)]
    (SCons outer-pat (SCons `(match b [~inner-pat ~field-lt _ false]) SNil))))

(defn- build-ord-sum-lt-go "Accumulator for building sum type < arms" [all-names :Int len remaining :Int idx acc]
  (match remaining
    [SNil acc
     (SCons ctor rest)
     (if (ctor-nullary? ctor)
       (let [name-sym $((ctor-name ctor))
             later (build-later-arms all-names len (+ idx 1) SNil)
             inner-arms (sconcat later (SCons (SexpSym "_") (SCons `false SNil)))
             arm-pair (SCons name-sym (SCons `(match b ~(SexpBracket inner-arms)) SNil))]
         (build-ord-sum-lt-go all-names len rest (+ idx 1) (sconcat acc arm-pair)))
       (let [name (ctor-name ctor)
             n (ctor-field-count ctor)
             abinds (make-bindings "__da" n)
             bbinds (make-bindings "__db" n)
             outer-pat (SexpList (SCons $name abinds))
             inner-pat (SexpList (SCons $name bbinds))
             field-lt (build-ord-lexico-chain abinds bbinds)
             later (build-later-arms all-names len (+ idx 1) SNil)
             inner-arms (sconcat (SCons inner-pat (SCons field-lt SNil))
                          (sconcat later (SCons (SexpSym "_") (SCons `false SNil))))
             arm-pair (SCons outer-pat (SCons `(match b ~(SexpBracket inner-arms)) SNil))]
         (build-ord-sum-lt-go all-names len rest (+ idx 1) (sconcat acc arm-pair))))]))

(defn- build-ord-sum-lt-arms "Build < arms for sum type" [ctors]
  (let [all-names (smap (fn [c] $((ctor-name c))) ctors)
        len (slength all-names)]
    (build-ord-sum-lt-go all-names len ctors 0 SNil)))

(defn- all-nullary? "Check if all constructors are nullary" [ctors]
  (match ctors
    [SNil true
     (SCons c rest) (if (ctor-nullary? c) (all-nullary? rest) false)]))

(defn- single-data-ctor? "Check if there is exactly one data constructor" [ctors]
  (match ctors
    [SNil false
     (SCons c rest)
     (if (ctor-nullary? c) false
       (if (sempty? rest) true false))]))

(defn- build-ord-lt-arms "Build < match arms based on type shape" [ctors]
  (if (all-nullary? ctors)
    (build-ord-enum-lt-arms ctors)
    (if (single-data-ctor? ctors)
      (build-ord-data-lt-arms (match ctors [(SCons c _) c _ (SexpSym "error")]))
      (build-ord-sum-lt-arms ctors))))

;; ── Layer 3: derive-Ord macro ──────────────────────────

(defmacro derive-Ord "Derive Ord trait implementation" [dt]
  `(impl Ord ~(build-impl-target (dt-name dt) (dt-params dt) "Ord" dt)
     (defn < [a b] (match a ~(SexpBracket (build-ord-lt-arms (dt-constructors dt)))))
     (defn > [a b] (< b a))))

;; ── Display helpers ────────────────────────────────────

(defn- build-show-nullary-arm "Build show arm for nullary ctor" [ctor]
  (let [name (ctor-name ctor)]
    (SCons $name (SCons (SexpStr name) SNil))))

(defn- build-show-fields "Build str-concat chain for showing fields" [binds]
  (match binds
    [SNil (SexpStr "")
     (SCons first rest)
     (let [first-show `(show ~first)
           rev-rest (sreverse rest)
           rest-expr (sfold (fn [acc b]
             (let [part `(str-concat ~(SexpStr " ") (show ~b))]
               (match acc
                 [(SexpStr _) part
                  _ `(str-concat ~part ~acc)])))
             (SexpStr "")
             rev-rest)]
       (match rest-expr
         [(SexpStr _) first-show
          _ `(str-concat ~first-show ~rest-expr)]))]))

(defn- build-show-data-arm "Build show arm for data ctor" [ctor]
  (let [name (ctor-name ctor)
        n (ctor-field-count ctor)
        binds (make-bindings "__d" n)
        pat (SexpList (SCons $name binds))
        fields-str (build-show-fields binds)
        result `(str-concat (str-concat ~(SexpStr (str-concat name "(")) ~fields-str) ~(SexpStr ")"))]
    (SCons pat (SCons result SNil))))

(defn- build-show-arms "Build all match arm pairs for Display" [ctors]
  (sfold (fn [acc ctor]
    (sconcat acc
      (if (ctor-nullary? ctor)
        (build-show-nullary-arm ctor)
        (build-show-data-arm ctor))))
    SNil ctors))

;; ── Layer 3: derive-Display macro ──────────────────────

(defmacro derive-Display "Derive Display trait implementation" [dt]
  `(impl Display ~(build-impl-target (dt-name dt) (dt-params dt) "Display" dt)
     (defn show [self] (match self ~(SexpBracket (build-show-arms (dt-constructors dt)))))))

;; ── Layer 3: derive dispatch macro ─────────────────────

(defmacro derive "Derive trait implementations for a type" [[& traits] dt]
  (let [calls (sfold
                (fn [acc trait-sexp]
                  (match trait-sexp
                    [(SexpSym name)
                     (SCons (SexpList (SCons $((str-concat "derive-" name))
                                            (SCons dt SNil)))
                            acc)
                     _ acc]))
                SNil traits)]
    (SexpList (SCons (SexpSym "begin") (SCons dt (sreverse calls))))))
