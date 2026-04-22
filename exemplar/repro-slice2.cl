;; repro-slice2.cl — Sprint 61 Slice 2, Branch (b) repro.
;;
;; ISOLATED COMPILER BUG: inline ADT constructor holding a Vec, passed as
;; a function argument, results in the Vec being corrupted (zero-length
;; or garbage) when the callee returns a derived ADT.
;;
;; Minimum trigger:
;;   (deftype Box [cells])                     ; ADT wrapping a Vec
;;   (defn consume [b] (box-set b 0 1))        ; callee performs vec-set
;;   (consume (Box [0]))                       ; INLINE ADT as argument — BUG
;;
;; Working:
;;   (let [b (Box [0])] (consume b))           ; let-bound first — OK
;;
;; Expected output:
;;   direct-let: len=1
;;   inline-arg: len=1   ; fails — shows len=0 under the bug
;;   let-arg:    len=1
;;
;; Observed (HEAD a9028c0, 2026-04-22, /port Slice 2):
;;   direct-let: len=1
;;   inline-arg: len=0   ; BUG
;;   let-arg:    len=1
;;
;; Handoff: /backend (consuming-arg RC emission for inline ADT constructors).
;; Hypothesis: the compiler emits the ADT constructor's inner allocation
;; with rc=1, then passes it to the callee under consuming convention,
;; where it is dec'd without the caller ever inc'ing to keep the inner
;; Vec alive — or the callee's match-unwrap dec's the Box's rc, freeing
;; the Vec while the callee still holds a field reference. /qa narrow
;; test should use the (consume (Box [0])) → len=1 shape.
;;
;; Relation to the Slice 2 `test-unsolvable` defect: adding the correct
;; Given/Solved same-value → None check in `solver.cl eliminate` causes
;; `test-unsolvable` to PASS but causes `test-easy-puzzle` and
;; `test-hard-puzzle` to FAIL (solver returns Unsolvable on valid
;; puzzles). The easy/hard regressions may be a DIFFERENT compiler bug
;; in the backtracking path (recursive `try-digits` with Grid/Vec
;; re-use across a match-arm backtrack), NOT the same as this repro.
;; The Sudoku solver passes a let-bound Grid (not an inline constructor),
;; so the trigger here does not directly match the Sudoku call sites.
;;
;; Per the Slice 2 2-day cap, /port hands off with:
;;  (1) This minimal non-Sudoku compiler-bug repro (inline-ADT-arg).
;;  (2) An open question: is the test-easy/hard regression under the
;;      semantic `eliminate` fix the SAME bug, a near relative, or
;;      unrelated? Reduction beyond this point in user-space code was
;;      inconclusive — see SPRINT.md readout for remaining shape.

(platform stdio)
(import [primitives [*]])
(import [platform.stdio [print]])
(import [primitives [bind Pure]])

(deftype Box [cells])

(defn box-set [b idx x] (match b [(Box v) (Box (vec-set v idx x))]))
(defn box-len [b] (match b [(Box v) (vec-len v)]))

(defn consume [b] (box-set b 0 1))

(defn int-to-digit [n]
  (if (eq-i64 n 0) "0"
  (if (eq-i64 n 1) "1"
  (if (eq-i64 n 2) "2"
  (if (eq-i64 n 3) "3" "?")))))

(defn main []
  (let [b1 (Box [0])
        r1 (box-set b1 0 1)
        len1 (box-len r1)
        ;; BUG trigger: inline (Box [0]) passed directly to consume.
        r2 (consume (Box [0]))
        len2 (box-len r2)
        ;; Workaround: let-bind the Box first.
        b3 (Box [0])
        r3 (consume b3)
        len3 (box-len r3)]
    (bind (print (str-concat "direct-let: len=" (int-to-digit len1)))
      (fn [_]
        (bind (print (str-concat "inline-arg: len=" (int-to-digit len2)))
          (fn [_]
            (print (str-concat "let-arg:    len=" (int-to-digit len3)))))))))
