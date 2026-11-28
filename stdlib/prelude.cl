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
;;   io.monad         — do, bind!
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
(export [io.monad     [do bind!]])
(export [control      [when unless cond case]])
(export [defs         [const const- def def-]])

;; ── Primitive TYPE re-exports ────────────────────────────────────────
;;
;; The four intrinsic scalar types are re-exported so that bare type refs
;; (`:Int`/`:Float`/`:Bool`/`:String` in `:Type` annotations, `deftype`
;; fields, and `deftrait` signatures) resolve without per-file imports.
;; spec 03-types.md §3.1: a bare type reference MUST be re-exported by the
;; prelude or explicitly imported; FQ `:primitives/Int` is always available.

(export [primitives [Int Bool Float String]])

;; ── Primitive FUNCTION re-exports ────────────────────────────────────
;;
;; The prelude re-exports no primitive function that has a curated name:
;; users write `+`, `=`, `show` and `str`, not `add-i64`, `eq-i64` or
;; `str-concat`. `pure` is the language's lift (spec §10.2) and has no curated
;; alternative, so it is re-exported as `primitives/pure`. Re-exporting the
;; primitive keeps one identity: a program that also imports `primitives/pure`
;; sees the same binding, not a second `pure`.
;;
;; Every primitive stays reachable as `primitives/<name>` or through
;; `(import [primitives [name]])`, and an empty prelude stays valid
;; (spec §3.1, §8.8.1, §8.9.1, §8.11.4).

(export [primitives [pure]])

;; ── Curated collection verbs (module-qualified, not re-exported) ─────
;;
;; `count`/`get`/`conj`/`assoc` and `map`/`filter`/`reduce` are not
;; re-exported here: the bare names are reserved until a collection trait owns
;; them (spec §11.4a). The list and pair `first` accessors are not re-exported
;; either, as a curation choice (plan-stdlib.md §1.5). Reach these verbs
;; module-qualified (`collections.vec/count`) or through an explicit import.
