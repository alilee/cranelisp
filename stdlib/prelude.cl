;; prelude.cl — Standard prelude for Cranelisp
;;
;; Pure re-export shell. No definitions — all macros and functions are
;; defined in their domain modules and re-exported here.
;;
;; Loaded implicitly for all non-prelude modules.
;;
;; Domain modules (traits, types, macros):
;;   compare.eq       — Eq trait + impls
;;   compare.ord      — Ord trait + impls
;;   num.num          — Num trait + impls
;;   text.display     — Display trait + impls
;;   text.string      — str macro + string operations
;;   fn.option        — Option type
;;   fn.result        — Result type
;;   fn.threading     — ->, ->> macros
;;   collections.list — List type + list macro
;;   collections.vec  — vec macro + Vec utilities
;;   io.monad         — pure, do, bind!
;;   control          — when, unless, cond, case
;;   defs             — const, const-, def, def-
;;
;; Spec references: 07-traits.md §7.1-7.4, 08-modules.md §8.4, 09-macros.md §9.5

;; ── Re-exports from domain modules ──────────────────────────────────

(export [compare.eq   [Eq = !=]])
(export [compare.ord  [Ord < > <= >=]])
(export [num.num      [Num + - * /]])
(export [text.display [Display show]])
(export [text.string  [str]])
(export [fn.option    [Option Some None]])
(export [fn.result    [Result Ok Err]])
(export [fn.threading [-> ->>]])
(export [collections.list [List Nil Cons empty? list]])
(export [collections.vec  [vec]])
(export [io.monad     [pure do bind!]])
(export [control      [when unless cond case]])
(export [defs         [const const- def def-]])

;; ── Primitive TYPE re-exports ────────────────────────────────────────
;;
;; The four intrinsic scalar types are re-exported so that bare type refs
;; (`:Int`/`:Float`/`:Bool`/`:String` in `:Type` annotations, `deftype`
;; fields, and `deftrait` signatures) resolve without per-file imports.
;; spec 03-types.md §3.1: a bare type reference MUST be re-exported by the
;; prelude or explicitly imported; FQ `:primitives/Int` is always available.
;; Mirrors examples/lib/prelude.cl:44. Without this, a stdlib-prelude program
;; using `(deftype P [:Int x])` or a bare `:Int 42` annotation errored with
;; `unknown type 'Int' (from module '')`.

(export [primitives [Int Bool Float String]])

;; ── Curated collection verbs (module-qualified, not re-exported) ─────
;;
;; `count`/`get`/`conj`/`assoc` and `map`/`filter`/`reduce` are not
;; re-exported here: the bare names are reserved until a collection trait owns
;; them (spec §11.4a). The list and pair `first` accessors are not re-exported
;; either, as a curation choice (plan-stdlib.md §1.5). Reach these verbs
;; module-qualified (`collections.vec/count`) or through an explicit import.

;; ── DE-LEAK LANDED (S86 step 1.5d) ───────────────────────────────────
;;
;; The ~31 raw-primitive bare re-exports (`add-i64`, `vec-get`,
;; `str-concat`, …) that previously lived here have been REMOVED. The
;; user now sees only the curated surface — `(+ a b)`, `(= a b)`,
;; `(!= a b)`, `(< a b)`, `(show x)`, `(count v)`, `(get v i)` — never the
;; bare raw primitives. This is the `print`→`platform.stdio/print`
;; re-export precedent (§8.4.7) applied to primitives.
;;
;; The de-leak was unblocked by two S86 compiler fixes:
;;   - D1 (/typecheck): trait default-method bodies (e.g. `Eq`'s `!=`,
;;     `Ord`'s `<=`) now resolve their free symbols in the trait's
;;     DEFINING module, not the caller's scope. Previously dropping the
;;     bare `add-i64` re-export made `(!= 1 2)` / `(<= 2 2)` fail with
;;     "undefined variable" because the default-method body resolved at the
;;     call site. (Mirror of `recheck_body_for_mono`, FIXME 0355.)
;;   - D2 (/backend): the `neq-string` primitive now exists, so String
;;     `!=` (`(!= "a" "b")`) monomorphises to a real symbol.
;;
;; The three curation invariants still hold (spec §8.9.1 / §8.11.4 / §3.1
;; / §8.8.1): FQ `primitives/<name>` stays reachable regardless of imports;
;; the empty prelude remains valid; nothing here is load-bearing. Raw
;; primitives reach via `(import [primitives [name]])` or `primitives/name`.
