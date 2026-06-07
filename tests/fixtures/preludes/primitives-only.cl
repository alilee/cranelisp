;; PreludeVariant::PrimitivesOnly — bare primitive names, no traits, no ADTs.
;;
;; Used by tests that need bare primitive access (add-i64, str-concat, etc.)
;; but no operator dispatch, no Option/Result, no Num/Eq/Ord.
;;
;; See `tests/plan/helpers-api.md` §"PreludeVariant".
;;
;; Spec §8.4: a re-EXPORT makes the primitive names PUBLIC on the prelude
;; module, so they flow through the user module's implicit prelude glob (§8.8)
;; as bare names. A plain `(import ...)` is Private and the glob (§8.7.3) would
;; skip it, leaving the user site with `undefined variable` — see FIXME 0263.

(export [primitives [*]])
