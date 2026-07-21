;; derive/helpers.cl — expansion-time helpers for the derive macros
;;
;; The `derive-Eq`/`derive-Ord`/`derive-Display` macros in `derive.cl` reference
;; these functions inside their expansions. Per spec §9.3.4 a macro's expansion
;; MUST NOT reference a same-module non-macro definition — such a helper MUST live
;; in a DEPENDENCY module. This module is that dependency: `derive.cl` declares it
;; via `(mod helpers)` and imports the seven public entry points, so every helper
;; is typechecked-and-compiled before the derive macros expand.
;;
;; These are ordinary functions calling ordinary functions; the §9.3.4 restriction
;; only governs macro-expansion-time references across the macro's own module
;; boundary, so intra-module forward/mutual references here are unrestricted. The
;; seven functions the macro bodies call directly are `defn` (public); the rest
;; stay `defn-` (private to this module).
;;
;; Uses primitives directly (no prelude dependency) since this module — like
;; `derive.cl` — is compiled outside the prelude graph.
;;
;; Spec: 07-traits.md §7.4, 09-macros.md §9.3.4, plan-stdlib.md §3.3

(import [prelude []])
(import [primitives [*]])

(import [macros [*]])
(import [core.syntax [sfold sreverse sempty? slist]])

;; ── Layer 1: SList utilities ───────────────────────────

(defn- slength "Count elements in an SList" [xs]
  (sfold (fn [acc _] (add-i64 acc 1)) 0 xs))

(defn- smap "Map a function over an SList" [f xs]
  (sreverse (sfold (fn [acc x] (SCons (f x) acc)) SNil xs)))

(defn- sdrop "Drop first n elements from an SList" [:Int n xs]
  (if (eq-i64 n 0) xs
    (match xs
      [SNil SNil
       (SCons _ t) (sdrop (sub-i64 n 1) t)])))

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

(defn dt-name "Extract type name string from deftype sexp" [dt]
  (let [head (dt-head dt)]
    (match head
      [(SexpSym s) s
       (SexpList items)
       (match items
         [(SCons first _)
          (match first [(SexpSym s) s _ "error-dt-name"])
          _ "error-dt-name"])
       _ "error-dt-name"])))

(defn dt-params "Extract type param names as SList of Strings" [dt]
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

(defn dt-constructors "Get constructor sexps as SList" [dt]
  (let [body (dt-body dt)]
    (match body
      [(SCons first _)
       (match first
         [(SexpBracket _)
          (SCons (SexpList (SCons (SexpSym (dt-name dt)) body)) SNil)
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
    (div-i64 (slength (ctor-fields-raw ctor)) 2)))

;; ── Layer 2: Sexp building helpers ─────────────────────

(defn- make-binding "Generate a single binding name like __da3" [:String prefix :Int i]
  (SexpSym (str-concat prefix (int-to-string i))))

(defn- make-bindings-acc "Accumulator helper for make-bindings" [:String prefix :Int n :Int i acc]
  (if (eq-i64 i n) acc
    (make-bindings-acc prefix n (add-i64 i 1) (SCons (make-binding prefix i) acc))))

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

;; ARITY CEILING (S115) — read before assuming a derive bug is in this file.
;;
;; These builders are correct but cannot RUN past a small arity, because the
;; SList/Sexp values they allocate corrupt the heap (FIXME 0835 — glibc
;; `free(): chunks in smallbin corrupted` from ~6 SList cells, reproducible in
;; ORDINARY code with no macro involved). The observable derive symptoms:
;;
;;   - any constructor with 2+ FIELDS → the compiler process dies silently
;;     (no diagnostic, REPL exits) for all three derive macros; 1 field is green
;;   - `derive-Ord` on a nullary enum with 3+ CONSTRUCTORS → macro-expansion
;;     "runtime panic: match failed"; 1 and 2 constructors are green
;;
;; Both were confirmed NOT to be defects in the generated code: hand-writing the
;; exact impl these builders emit — the 2-field `Eq` and the 3-arm nested-match
;; `Ord` — compiles and evaluates correctly. Only BUILDING it fails.
;;
;; So do not "fix" these builders by reshaping them. Two reshapes were tried and
;; neither moved the ceiling (replacing the `snth` index walk with a tail walk;
;; hoisting every quasiquote out of its enclosing closure into a named `defn-`).
;; Both are RETAINED below because they are better code, not because they cured
;; anything. `derive/test.cl` covers exactly the arities that work and says so.

;; (Retained from the S115 pass: quasiquote-bearing fold steps are named
;; `defn-`s and the closure only calls them.)

(defn- eq-chain-step "One (a b) pair of the Eq field-equality chain" [inner pair]
  (match pair
    [(SCons a rest)
     (match rest
       [(SCons b _) `(if (= ~a ~b) ~inner false)
        _ inner])
     _ inner]))

(defn- build-eq-chain "Build (if (= a0 b0) (if (= a1 b1) ... true) false) from two SLists" [as bs]
  (sfold (fn [inner pair] (eq-chain-step inner pair))
         `true
         (szip-rev-acc as bs SNil)))

(defn- build-eq-nullary-arm "Build match arm pair for nullary ctor in Eq" [ctor]
  (let [s (SexpSym (ctor-name ctor))]
    (SCons s (SCons `(match b [~s true _ false]) SNil))))

(defn- build-eq-data-arm "Build match arm pair for data ctor in Eq" [ctor]
  (let [name (ctor-name ctor)
        n (ctor-field-count ctor)
        abinds (make-bindings "__da" n)
        bbinds (make-bindings "__db" n)
        outer-pat (SexpList (SCons (SexpSym name) abinds))
        inner-pat (SexpList (SCons (SexpSym name) bbinds))
        field-eq (build-eq-chain abinds bbinds)]
    (SCons outer-pat (SCons `(match b [~inner-pat ~field-eq _ false]) SNil))))

(defn build-eq-arms "Build all match arm pairs for Eq" [ctors]
  (sfold (fn [acc ctor]
    (macros/sconcat acc
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
     (SCons h t) (if (str-eq h needle) true (scontains? needle t))]))

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

(defn build-impl-target "Build impl target sexp with constraints" [:String name params :String trait-name dt]
  (if (sempty? params)
    (SexpSym name)
    (let [constrained (dt-constraints-for-trait trait-name params dt)
          param-sexps (smap (fn [p]
            (let [colon-p (str-concat ":" p)]
              (if (scontains? colon-p constrained)
                (slist (SexpSym (str-concat ":" trait-name)) (SexpSym p))
                (slist (SexpSym p)))))
            params)]
      (SexpList (SCons (SexpSym name) (sfold (fn [a b] (macros/sconcat a b)) SNil param-sexps))))))

;; ── Ord helpers ────────────────────────────────────────

;; The "later constructors" of a ctor are exactly the TAIL of the ctor list at
;; that point — walk it directly. (Pre-S115 this indexed into a materialised
;; name list with `snth i` for i in [idx+1, len), an O(n²) walk with an
;; out-of-bounds sentinel arm; the tail is already in hand at every call site.)
(defn- later-arm "The (name true) arm pair for one later constructor" [c]
  (SCons (SexpSym (ctor-name c)) (SCons `true SNil)))

(defn- build-later-arms "Build (name true) arm pairs for the constructors AFTER the current one" [later-ctors]
  (sfold (fn [acc c] (macros/sconcat acc (later-arm c))) SNil later-ctors))

(defn- build-ord-enum-lt-go "Accumulator for building enum < arms" [remaining acc]
  (match remaining
    [SNil acc
     (SCons ctor rest)
     (let [name-sym (SexpSym (ctor-name ctor))
           later (build-later-arms rest)
           inner-arms (macros/sconcat later (SCons (SexpSym "_") (SCons `false SNil)))
           arm-pair (SCons name-sym (SCons `(match b ~(SexpBracket inner-arms)) SNil))]
       (build-ord-enum-lt-go rest (macros/sconcat acc arm-pair)))]))

(defn- build-ord-enum-lt-arms "Build < arms for enum: each ctor is less than later ones" [ctors]
  (build-ord-enum-lt-go ctors SNil))

(defn- ord-chain-step "One (a b) pair of the lexicographic < chain" [inner pair]
  (match pair
    [(SCons a rest)
     (match rest
       [(SCons b _) `(if (< ~a ~b) true (if (= ~a ~b) ~inner false))
        _ inner])
     _ inner]))

(defn- build-ord-lexico-chain "Build lexicographic < comparison from two binding lists" [as bs]
  (sfold (fn [inner pair] (ord-chain-step inner pair))
         `false
         (szip-rev-acc as bs SNil)))

(defn- build-ord-data-lt-arms "Build < arms for data ctor with fields" [ctor]
  (let [name (ctor-name ctor)
        n (ctor-field-count ctor)
        abinds (make-bindings "__da" n)
        bbinds (make-bindings "__db" n)
        outer-pat (SexpList (SCons (SexpSym name) abinds))
        inner-pat (SexpList (SCons (SexpSym name) bbinds))
        field-lt (build-ord-lexico-chain abinds bbinds)]
    (SCons outer-pat (SCons `(match b [~inner-pat ~field-lt _ false]) SNil))))

(defn- build-ord-sum-lt-go "Accumulator for building sum type < arms" [remaining acc]
  (match remaining
    [SNil acc
     (SCons ctor rest)
     (if (ctor-nullary? ctor)
       (let [name-sym (SexpSym (ctor-name ctor))
             later (build-later-arms rest)
             inner-arms (macros/sconcat later (SCons (SexpSym "_") (SCons `false SNil)))
             arm-pair (SCons name-sym (SCons `(match b ~(SexpBracket inner-arms)) SNil))]
         (build-ord-sum-lt-go rest (macros/sconcat acc arm-pair)))
       (let [name (ctor-name ctor)
             n (ctor-field-count ctor)
             abinds (make-bindings "__da" n)
             bbinds (make-bindings "__db" n)
             outer-pat (SexpList (SCons (SexpSym name) abinds))
             inner-pat (SexpList (SCons (SexpSym name) bbinds))
             field-lt (build-ord-lexico-chain abinds bbinds)
             later (build-later-arms rest)
             inner-arms (macros/sconcat (SCons inner-pat (SCons field-lt SNil))
                          (macros/sconcat later (SCons (SexpSym "_") (SCons `false SNil))))
             arm-pair (SCons outer-pat (SCons `(match b ~(SexpBracket inner-arms)) SNil))]
         (build-ord-sum-lt-go rest (macros/sconcat acc arm-pair))))]))

(defn- build-ord-sum-lt-arms "Build < arms for sum type" [ctors]
  (build-ord-sum-lt-go ctors SNil))

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

(defn build-ord-lt-arms "Build < match arms based on type shape" [ctors]
  (if (all-nullary? ctors)
    (build-ord-enum-lt-arms ctors)
    (if (single-data-ctor? ctors)
      (build-ord-data-lt-arms (match ctors [(SCons c _) c _ (SexpSym "error")]))
      (build-ord-sum-lt-arms ctors))))

;; ── Display helpers ────────────────────────────────────

(defn- build-show-nullary-arm "Build show arm for nullary ctor" [ctor]
  (let [name (ctor-name ctor)]
    (SCons (SexpSym name) (SCons (SexpStr name) SNil))))

(defn- show-field-step "Prepend one space-separated (show b) to the accumulated tail" [acc b]
  (let [part `(str-concat ~(SexpStr " ") (show ~b))]
    (match acc
      [(SexpStr _) part
       _ `(str-concat ~part ~acc)])))

(defn- build-show-fields "Build str-concat chain for showing fields" [binds]
  (match binds
    [SNil (SexpStr "")
     (SCons first rest)
     (let [first-show `(show ~first)
           rest-expr (sfold (fn [acc b] (show-field-step acc b))
                            (SexpStr "")
                            (sreverse rest))]
       (match rest-expr
         [(SexpStr _) first-show
          _ `(str-concat ~first-show ~rest-expr)]))]))

(defn- build-show-data-arm "Build show arm for data ctor" [ctor]
  (let [name (ctor-name ctor)
        n (ctor-field-count ctor)
        binds (make-bindings "__d" n)
        pat (SexpList (SCons (SexpSym name) binds))
        fields-str (build-show-fields binds)
        result `(str-concat (str-concat ~(SexpStr (str-concat name "(")) ~fields-str) ~(SexpStr ")"))]
    (SCons pat (SCons result SNil))))

(defn build-show-arms "Build all match arm pairs for Display" [ctors]
  (sfold (fn [acc ctor]
    (macros/sconcat acc
      (if (ctor-nullary? ctor)
        (build-show-nullary-arm ctor)
        (build-show-data-arm ctor))))
    SNil ctors))
