;; solver.cl — Sudoku constraint propagation and backtracking solver
;;
;; Implements:
;; - eliminate: remove a digit from a cell's candidates
;; - propagate: iterate constraint elimination to fixpoint
;; - find-min-candidates: MRV heuristic for backtracking
;; - solve: main solver combining propagation and backtracking
;;
;; Depends on: grid.cl (Cell, Grid, SolveResult, bitmask ops, peers)
;; Depends on: prelude (Option, macros)
;;
;; NOTE: This file depends on F2 string primitives (char-at) indirectly
;; through grid.cl's make-grid. The solver logic itself only uses Int
;; and Vec operations.

(import [grid [Grid Cell Given Solved Candidates SolveResult Success Unsolvable
               full-mask bit-set? bit-clear bit-count bit-lowest
               cell-at set-cell peers is-solved cell-determined? make-grid]])

;; ── Constraint Propagation ─────────────────────────────────────────────

;; Eliminate digit d from the candidates of cell at index idx.
;; Returns (Some grid) on success, None on contradiction.
;;
;; If the cell is Given or Solved, no change needed.
;; If it's Candidates:
;;   - Clear the digit from the bitmask
;;   - If bitmask becomes 0: contradiction (no candidates left)
;;   - If bitmask has exactly 1 bit: cell is determined -> Solved
;;   - Otherwise: cell still has multiple candidates
(defn eliminate [g idx d]
  (let [cell (cell-at g idx)]
    (match cell
      [(Given _) (Some g)
       (Solved _) (Some g)
       (Candidates mask)
         (if (not (bit-set? mask d))
           ;; Digit not in candidates, no change
           (Some g)
           (let [new-mask (bit-clear mask d)]
             (if (eq-i64 new-mask 0)
               ;; Contradiction: no candidates left
               None
               (if (eq-i64 (bit-count new-mask) 1)
                 ;; Determined: exactly one candidate remains
                 (Some (set-cell g idx (Solved (bit-lowest new-mask))))
                 ;; Reduced: still multiple candidates
                 (Some (set-cell g idx (Candidates new-mask)))))))])))

;; Eliminate a digit from all peers of a given cell.
;; Used when a cell becomes determined (Given or Solved with value d).
;; Returns (Some grid) on success, None if any elimination causes contradiction.
(defn eliminate-from-peers-helper [g peer-list d i]
  (if (eq-i64 i (vec-len peer-list)) (Some g)
    (let [peer-idx (vec-get peer-list i)]
      (match (eliminate g peer-idx d)
        [None None
         (Some g2) (eliminate-from-peers-helper g2 peer-list d (add-i64 i 1))]))))

(defn eliminate-from-peers [g idx d]
  (eliminate-from-peers-helper g (peers idx) d 0))

;; Single pass of constraint propagation:
;; For every determined cell (Given or Solved), eliminate its value
;; from all peers' candidates.
;;
;; Returns (Some grid) with propagated constraints, or None on contradiction.
(defn propagate-pass-helper [g i]
  (if (eq-i64 i 81) (Some g)
    (let [cell (cell-at g i)]
      (match cell
        [(Given v)
           (match (eliminate-from-peers g i v)
             [None None
              (Some g2) (propagate-pass-helper g2 (add-i64 i 1))])
         (Solved v)
           (match (eliminate-from-peers g i v)
             [None None
              (Some g2) (propagate-pass-helper g2 (add-i64 i 1))])
         (Candidates _)
           (propagate-pass-helper g (add-i64 i 1))]))))

;; Check if any cell was changed during propagation by comparing
;; candidate masks. Returns true if grids differ.
(defn grids-differ-helper [g1 g2 i]
  (if (eq-i64 i 81) false
    (let [c1 (cell-at g1 i)
          c2 (cell-at g2 i)]
      ;; Compare cells: if both are Candidates, compare masks
      (match c1
        [(Candidates m1)
           (match c2
             [(Candidates m2) (if (eq-i64 m1 m2)
                                (grids-differ-helper g1 g2 (add-i64 i 1))
                                true)
              _ true])
         (Given _)
           (match c2
             [(Given _) (grids-differ-helper g1 g2 (add-i64 i 1))
              _ true])
         (Solved _)
           (match c2
             [(Solved _) (grids-differ-helper g1 g2 (add-i64 i 1))
              _ true])]))))

;; Propagate constraints to fixpoint.
;; Repeatedly applies propagate-pass until no changes occur or contradiction.
(defn propagate [g]
  (match (propagate-pass-helper g 0)
    [None None
     (Some g2)
       (if (grids-differ-helper g g2 0)
         ;; Something changed, keep propagating
         (propagate g2)
         ;; No change, fixpoint reached
         (Some g2))]))

;; ── MRV Heuristic ──────────────────────────────────────────────────────

;; Find the index of the unfixed cell with the fewest candidates.
;; This is the Minimum Remaining Values (MRV) heuristic.
;; Returns (Some idx) or None if all cells are determined.
(defn find-min-helper [g i best-idx best-count]
  (if (eq-i64 i 81)
    (if (eq-i64 best-idx -1) None (Some best-idx))
    (let [cell (cell-at g i)]
      (match cell
        [(Candidates mask)
           (let [cnt (bit-count mask)]
             (if (if (eq-i64 best-idx -1) true (lt-i64 cnt best-count))
               (find-min-helper g (add-i64 i 1) i cnt)
               (find-min-helper g (add-i64 i 1) best-idx best-count)))
         (Given _) (find-min-helper g (add-i64 i 1) best-idx best-count)
         (Solved _) (find-min-helper g (add-i64 i 1) best-idx best-count)]))))

(defn find-min-candidates [g]
  (find-min-helper g 0 -1 10))

;; ── Backtracking Solver ────────────────────────────────────────────────

;; Try each digit d from lo to 9 at the given cell index.
;; Returns the first successful solution or Unsolvable.
(defn try-digits [g idx mask d]
  (if (gt-i64 d 9) Unsolvable
    (if (not (bit-set? mask d))
      ;; Digit not a candidate, skip
      (try-digits g idx mask (add-i64 d 1))
      ;; Try setting this cell to d and solving
      (let [g2 (set-cell g idx (Solved d))]
        (match (solve g2)
          [(Success solution) (Success solution)
           Unsolvable (try-digits g idx mask (add-i64 d 1))])))))

;; Main solver: propagate, then backtrack if needed.
;;
;; Algorithm:
;; 1. Propagate constraints
;; 2. If contradiction -> Unsolvable
;; 3. If all cells determined -> Success
;; 4. Otherwise: pick cell with fewest candidates (MRV),
;;    try each candidate recursively
(defn solve [g]
  (match (propagate g)
    [None Unsolvable
     (Some g2)
       (if (is-solved g2)
         (Success g2)
         ;; Need to guess: find cell with minimum candidates
         (match (find-min-candidates g2)
           [None
              ;; No unfixed cells but is-solved returned false?
              ;; This shouldn't happen, but handle gracefully.
              Unsolvable
            (Some idx)
              (let [cell (cell-at g2 idx)]
                (match cell
                  [(Candidates mask) (try-digits g2 idx mask 1)
                   _ Unsolvable]))]))]))

;; ── Tests ───────────────────────────────────────────────────────────────

(mod test
  (import [super [*]])
  (import [grid [Grid Cell Given Solved Candidates SolveResult Success Unsolvable
                 full-mask bit-set? bit-clear bit-count bit-lowest
                 cell-at set-cell peers is-solved cell-determined? make-grid]])

  ;; --- Helper to count determined cells ---
  (defn count-determined-helper [g i acc]
    (if (eq-i64 i 81) acc
      (if (cell-determined? (cell-at g i))
        (count-determined-helper g (add-i64 i 1) (add-i64 acc 1))
        (count-determined-helper g (add-i64 i 1) acc))))

  (defn count-determined [g]
    (count-determined-helper g 0 0))

  ;; --- Elimination tests (don't need make-grid) ---

  ;; Build a simple grid: cell 0 is Candidates full-mask, rest are Given 1
  (defn make-test-grid-one-candidate []
    (let [cells (let [v []]
                  (let [build (fn [v2 i2]
                    (if (eq-i64 i2 81) v2
                      (if (eq-i64 i2 0)
                        (build (vec-push v2 (Candidates full-mask)) (add-i64 i2 1))
                        (build (vec-push v2 (Given 1)) (add-i64 i2 1)))))]
                    (build v 0)))]
      (Grid cells)))

  (defn test-eliminate-removes-digit []
    ;; Eliminate digit 5 from cell 0 (which has full-mask)
    (let [g (make-test-grid-one-candidate)]
      (match (eliminate g 0 5)
        [(Some g2)
           (match (cell-at g2 0)
             [(Candidates m) (if (not (bit-set? m 5)) 1 0)
              _ 0])
         None 0])))

  (defn test-eliminate-no-effect-on-given []
    ;; Eliminating from a Given cell should be a no-op
    (let [g (make-test-grid-one-candidate)]
      (match (eliminate g 1 5)
        [(Some _) 1
         None 0])))

  (defn test-eliminate-determines-cell []
    ;; Start with only digits 3 and 7 as candidates (mask = 4 + 64 = 68)
    ;; Eliminate 7 -> should determine cell as 3
    (let [cells (let [v []]
                  (let [build (fn [v2 i2]
                    (if (eq-i64 i2 81) v2
                      (if (eq-i64 i2 0)
                        (build (vec-push v2 (Candidates 68)) (add-i64 i2 1))
                        (build (vec-push v2 (Given 1)) (add-i64 i2 1)))))]
                    (build v 0)))
          g (Grid cells)]
      (match (eliminate g 0 7)
        [(Some g2)
           (match (cell-at g2 0)
             [(Solved v) (if (eq-i64 v 3) 1 0)
              _ 0])
         None 0])))

  (defn test-eliminate-contradiction []
    ;; Cell with only digit 5 (mask = 16). Eliminate 5 -> contradiction.
    (let [cells (let [v []]
                  (let [build (fn [v2 i2]
                    (if (eq-i64 i2 81) v2
                      (if (eq-i64 i2 0)
                        (build (vec-push v2 (Candidates 16)) (add-i64 i2 1))
                        (build (vec-push v2 (Given 1)) (add-i64 i2 1)))))]
                    (build v 0)))
          g (Grid cells)]
      (match (eliminate g 0 5)
        [None 1
         _ 0])))

  ;; --- Solver tests (depend on make-grid -> F2) ---
  ;; These tests use make-grid which requires char-at.
  ;; They will fail until F2 string primitives land.

  ;; Known easy puzzle
  ;; Source: https://projecteuler.net/problem=96
  (defn test-easy-puzzle []
    (match (make-grid "003020600900305001001806400008102900700000008006708200002609500800203009005010300")
      [(Some g)
         (match (solve g)
           [(Success solution)
              ;; Verify all 81 cells are determined
              (if (eq-i64 (count-determined solution) 81) 1 0)
            Unsolvable 0])
       None 0]))

  ;; Known hard puzzle
  ;; Source: "World's hardest Sudoku" by Arto Inkala
  (defn test-hard-puzzle []
    (match (make-grid "800000000003600000070090200050007000000045700000100030001000068008500010090000400")
      [(Some g)
         (match (solve g)
           [(Success solution)
              (if (eq-i64 (count-determined solution) 81) 1 0)
            Unsolvable 0])
       None 0]))

  ;; Unsolvable puzzle: two 5s in the first row
  (defn test-unsolvable []
    (match (make-grid "550000000000000000000000000000000000000000000000000000000000000000000000000000000")
      [(Some g)
         (match (solve g)
           [(Success _) 0
            Unsolvable 1])
       None 0]))

  ;; --- Main: sum all test results ---

  (defn main []
    (add-i64 (test-eliminate-removes-digit)
      (add-i64 (test-eliminate-no-effect-on-given)
        (add-i64 (test-eliminate-determines-cell)
          (add-i64 (test-eliminate-contradiction)
            ;; The following 3 tests depend on F2 (char-at via make-grid).
            ;; They will pass once F2 lands.
            (add-i64 (test-easy-puzzle)
              (add-i64 (test-hard-puzzle)
                (test-unsolvable)))))))))
