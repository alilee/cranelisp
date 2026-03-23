;; seq.cl — Lazy sequence group
;;
;; Provides the Seq type for lazy evaluation through thunks.
;; All definitions live in seq/lazy.cl to avoid circular module deps.
;;
;; Spec: 12-runtime.md §12.4.2, plan-stdlib.md §3.3

(mod lazy)

(export [lazy [Seq SeqNil SeqCons
               seq-empty? seq-map seq-filter seq-reduce
               range-from iterate repeat cycle
               seq-take seq-drop seq-nth take-while drop-while
               to-list to-vec seq-zip-with
               take drop]])
