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

;; ── Primitive re-exports ─────────────────────────────────────────────
;;
;; Ring 0/1 named primitives are re-exported through the prelude so that
;; `cargo run -- --run examples/FOO.cl` matches the REPL user surface.
;; These coexist with the trait-dispatched operators above (e.g. + and
;; add-i64 both work). See design/stdlib/examples-run-path.md for the
;; decision rationale.

(export [primitives [add-i64 sub-i64 mul-i64 div-i64 eq-i64 lt-i64 gt-i64 le-i64 ge-i64 not eq-bool]])
(export [primitives [add-f64 sub-f64 mul-f64 div-f64 eq-f64 lt-f64 gt-f64 le-f64 ge-f64]])
(export [primitives [str-concat str-eq str-len char-at int-to-string float-to-string bool-to-string]])
(export [primitives [vec-len vec-get vec-set vec-push]])
