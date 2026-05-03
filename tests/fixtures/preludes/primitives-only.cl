;; PreludeVariant::PrimitivesOnly — bare primitive names, no traits, no ADTs.
;;
;; Used by tests that need bare primitive access (add-i64, str-concat, etc.)
;; but no operator dispatch, no Option/Result, no Num/Eq/Ord.
;;
;; See `tests/plan/helpers-api.md` §"PreludeVariant".

(import [primitives [*]])
