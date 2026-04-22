;; test-eliminate-contract.cl — Sprint 61 Slice 2 Layer 1 contract test.
;;
;; Owned by /qa as a test fixture driving exemplar/solver.cl::eliminate.
;;
;; CONTRACT (per exemplar/solver.cl:370+ FIXME block, Layer 1):
;;   `eliminate` on a cell that is already `(Given v)` or `(Solved v)`
;;   with the SAME value as the digit d being eliminated MUST return
;;   `None` — eliminating the cell's own fixed value is a contradiction.
;;
;; Current buggy behaviour (a9028c0): the Given/Solved match arms return
;; `(Some g)` unconditionally. The one-line Layer 1 fix in solver.cl is
;;   (Given v)  (if (eq-i64 v d) None (Some g))
;;   (Solved v) (if (eq-i64 v d) None (Some g))
;; but applying it alone regresses valid puzzles via the Layer 2
;; compiler bug (see exemplar/repro-slice2.cl + solver.cl FIXMEs).
;;
;; EXIT CODE:
;;   0 — pass: `(eliminate g 0 5)` on a `(Given 5)` at cell 0 returned None
;;   1 — fail: `(eliminate g 0 5)` returned `(Some _)` (current buggy state)
;;   2 — setup failure (unexpected — make-test-given-grid misbehaved)
;;
;; This test does NOT require Sudoku-solver machinery — no `solve`, no
;; `propagate`, no puzzle string. It is the minimal contract assertion
;; against `eliminate` alone.

(platform stdio)
(import [primitives [*]])

(import [grid [Grid Cell Given Solved Candidates
               cell-at set-cell]])
(import [solver [eliminate]])

;; Build a grid where cell 0 is (Given 5) and the remaining 80 cells are
;; (Given 1). All cells are Given so no Candidates appear. This is not
;; a legal Sudoku grid, but the test only exercises cell 0.
(defn build-grid-given-5-helper [v i]
  (if (eq-i64 i 81) v
    (if (eq-i64 i 0)
      (build-grid-given-5-helper (vec-push v (Given 5)) (add-i64 i 1))
      (build-grid-given-5-helper (vec-push v (Given 1)) (add-i64 i 1)))))

(defn make-given-5-grid []
  (Grid (build-grid-given-5-helper [] 0)))

(defn main []
  (let [g (make-given-5-grid)]
    ;; Setup sanity: cell 0 should be (Given 5).
    (match (cell-at g 0)
      [(Given v)
         (if (eq-i64 v 5)
           ;; Setup OK. Now exercise the contract.
           (match (eliminate g 0 5)
             [None 0
              (Some _) 1])
           2)
       _ 2])))
