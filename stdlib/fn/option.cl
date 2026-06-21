;; fn/option.cl — Option type
;;
;; The Option type represents a value that may or may not be present.
;; None indicates absence; Some wraps a present value.
;;
;; `Option` is seeded by `primitives` (it is referenced by primitive
;; signatures such as `parse-int :: (Fn [String] (Option Int))` and the
;; no-stdlib REPL path needs bare `Some`/`None`). To keep ONE canonical
;; `Option` type across the system, this module RE-EXPORTS the primitives
;; `Option`/`Some`/`None` rather than defining a second, distinct ADT.
;;
;; This makes `fn.option/Option` the SAME type as `primitives/Option`, so a
;; module that both globs `primitives` and explicitly imports `fn.option`
;; deduplicates the overlapping names (spec §8.6.4 — same-source duplicates
;; are NOT ambiguous) instead of colliding on two distinct `Option`s.
;;
;; Spec: 06-adt.md §6.1, 08-modules.md §8.6.4

(import [prelude []])
(import [primitives [Option Some None]])
(export [primitives [Option Some None]])

;; ── Self-tests ───────────────────────────────────────────────────────
;; `(mod test …)` submodule (S87 Stage C.2). HARNESS-FREE: `testing.assertions`
;; depends on `fn.option` (it returns `(Option String)`), so importing the
;; harness here would form a load cycle. Tests construct/match Some & None
;; and return `(Option String)` directly.

(mod test)
