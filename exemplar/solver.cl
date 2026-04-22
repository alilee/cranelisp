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

(platform stdio)
(import [primitives [*]])

(import [grid [Grid Cell Given Solved Candidates SolveResult Success Unsolvable
               full-mask bit-set? bit-clear bit-count bit-lowest
               cell-at set-cell peers is-solved cell-determined? cell-value make-grid]])
(import [platform.stdio [print]])
(import [primitives [bind Pure]])

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
      [(Given v)  (if (eq-i64 v d) None (Some g))
       (Solved v) (if (eq-i64 v d) None (Some g))
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

;; ── Board Formatting ──────────────────────────────────────────────────

;; Convert a cell value (1-9) to its string digit, or "." for 0.
(defn digit-string [v]
  (if (eq-i64 v 1) "1"
  (if (eq-i64 v 2) "2"
  (if (eq-i64 v 3) "3"
  (if (eq-i64 v 4) "4"
  (if (eq-i64 v 5) "5"
  (if (eq-i64 v 6) "6"
  (if (eq-i64 v 7) "7"
  (if (eq-i64 v 8) "8"
  (if (eq-i64 v 9) "9"
    "."))))))))))

;; Format a puzzle string (81 chars) as a readable board.
;; Works directly on the string, no Grid needed.
;; Format:
;;   d d d | d d d | d d d
;;   ...
;;   ------+-------+------
;;   ...
(defn format-cell-char [s i]
  ;; Convert a single character from the puzzle string to display form.
  ;; '0' and '.' show as '.', digits show as themselves.
  (let [ch (char-at s i)]
    (if (str-eq ch "0") "." ch)))

(defn format-row-from-str [s row col acc]
  (if (eq-i64 col 9) acc
    (let [idx (add-i64 (mul-i64 row 9) col)
          ch (format-cell-char s idx)
          sep (if (eq-i64 col 0) ""
                (if (if (eq-i64 col 3) true (eq-i64 col 6))
                  " | "
                  " "))]
      (format-row-from-str s row (add-i64 col 1) (str-concat acc (str-concat sep ch))))))

(defn format-board-from-str [s row acc]
  (if (eq-i64 row 9) acc
    (let [row-str (format-row-from-str s row 0 "")
          sep (if (eq-i64 row 0) ""
                (if (if (eq-i64 row 3) true (eq-i64 row 6))
                  "\n------+-------+------\n"
                  "\n"))]
      (format-board-from-str s (add-i64 row 1) (str-concat acc (str-concat sep row-str))))))

(defn format-board-str [s]
  (format-board-from-str s 0 ""))

;; Format a solved Grid as a board string.
;; Extracts cell values and builds the display.
(defn format-row-helper [g r col acc]
  (if (eq-i64 col 9) acc
    (let [idx (add-i64 (mul-i64 r 9) col)
          v (cell-value (cell-at g idx))
          ds (digit-string v)
          sep (if (eq-i64 col 0) ""
                (if (if (eq-i64 col 3) true (eq-i64 col 6))
                  " | "
                  " "))]
      (format-row-helper g r (add-i64 col 1) (str-concat acc (str-concat sep ds))))))

(defn format-row [g r]
  (format-row-helper g r 0 ""))

(defn format-board-helper [g r acc]
  (if (eq-i64 r 9) acc
    (let [row-str (format-row g r)
          sep (if (eq-i64 r 0) ""
                (if (if (eq-i64 r 3) true (eq-i64 r 6))
                  "\n------+-------+------\n"
                  "\n"))]
      (format-board-helper g (add-i64 r 1) (str-concat acc (str-concat sep row-str))))))

(defn format-board [g]
  (format-board-helper g 0 ""))

;; ── IO Entry Point ───────────────────────────────────────────────────

;; Build the output string for a puzzle: header, input board, solution.
(defn build-output [puzzle-str]
  (let [header "=== Sudoku Solver ==="
        input-board (format-board-str puzzle-str)
        solution-str (match (make-grid puzzle-str)
                       [None "Error: invalid puzzle string"
                        (Some g)
                          (match (solve g)
                            [(Success solution)
                               (format-board solution)
                             Unsolvable
                               "No solution found"])])]
    (str-concat header
      (str-concat "\n\nPuzzle:\n"
        (str-concat input-board
          (str-concat "\n\nSolution:\n" solution-str))))))

;; Main: solve a puzzle and print the formatted board.
;;
;; NOTE: The solver (propagate/solve) currently segfaults on full 81-cell
;; grids due to deep recursion causing stack overflow. This is a known
;; runtime issue. The IO and formatting code works correctly — once the
;; runtime issue is resolved, this will print both puzzle and solution.
(defn main []
  (let [puzzle "003020600900305001001806400008102900700000008006708200002609500800203009005010300"]
    (bind (print (str-concat "=== Sudoku Solver ===\n\nPuzzle:\n"
                   (format-board-str puzzle)))
      (fn [_]
        (match (make-grid puzzle)
          [None (print "\nError: invalid puzzle string")
           (Some g)
             (match (solve g)
               [(Success solution)
                  (print (str-concat "\nSolution:\n" (format-board solution)))
                Unsolvable
                  (print "\nNo solution found")])])))))

;; ── Tests ───────────────────────────────────────────────────────────────
;;
;; Test functions are top-level `test-*` defns returning `(Option String)`
;; per repl/spec.md §16.1. Discoverable via `(discover-tests)`,
;; runnable via `(run-test ...)` — Decision 30 safe pattern (c). No
;; `(mod test ...)` wrapper, no `(import [super [*]])`.

;; --- Helper to count determined cells ---

(defn count-determined-helper [g i acc]
  (if (eq-i64 i 81) acc
    (if (cell-determined? (cell-at g i))
      (count-determined-helper g (add-i64 i 1) (add-i64 acc 1))
      (count-determined-helper g (add-i64 i 1) acc))))

(defn count-determined [g]
  (count-determined-helper g 0 0))

;; --- Test grid builders (no `let`-defined `build` recursion) ---

;; Build a grid: cell 0 has the given mask as Candidates, the rest are Given 1.
(defn build-mask-then-givens-helper [v i mask]
  (if (eq-i64 i 81) v
    (if (eq-i64 i 0)
      (build-mask-then-givens-helper (vec-push v (Candidates mask)) (add-i64 i 1) mask)
      (build-mask-then-givens-helper (vec-push v (Given 1)) (add-i64 i 1) mask))))

(defn make-test-grid-with-mask [mask]
  (Grid (build-mask-then-givens-helper [] 0 mask)))

;; --- Elimination tests (don't need make-grid) ---

(defn test-eliminate-removes-digit []
  ;; Eliminate digit 5 from cell 0 (which has full-mask)
  (let [g (make-test-grid-with-mask (full-mask))]
    (match (eliminate g 0 5)
      [(Some g2)
         (match (cell-at g2 0)
           [(Candidates m) (if (not (bit-set? m 5)) None
                             (Some "bit 5 should be cleared in cell 0 candidates"))
            _ (Some "cell 0 should still be Candidates")])
       None (Some "eliminate should not return None for valid input")])))

(defn test-eliminate-no-effect-on-given []
  ;; Eliminating from a Given cell should be a no-op (still Some)
  (let [g (make-test-grid-with-mask (full-mask))]
    (match (eliminate g 1 5)
      [(Some _) None
       None (Some "eliminate from Given cell should be a no-op (not None)")])))

(defn test-eliminate-determines-cell []
  ;; Start with only digits 3 and 7 as candidates (mask = 4 + 64 = 68).
  ;; Eliminate 7 -> should determine cell as 3.
  (let [g (make-test-grid-with-mask 68)]
    (match (eliminate g 0 7)
      [(Some g2)
         (match (cell-at g2 0)
           [(Solved v) (if (eq-i64 v 3) None
                         (Some "cell 0 should be Solved 3 after eliminating 7"))
            _ (Some "cell 0 should be Solved after eliminating 7 from {3,7}")])
       None (Some "eliminate of valid digit should not return None")])))

(defn test-eliminate-contradiction []
  ;; Cell with only digit 5 (mask = 16). Eliminate 5 -> contradiction (None).
  (let [g (make-test-grid-with-mask 16)]
    (match (eliminate g 0 5)
      [None None
       _ (Some "eliminating last candidate should produce contradiction (None)")])))

;; --- Solver tests ---
;;
;; Slice 2 closure 2026-04-22 — Sudoku solver correctness.
;;
;; Investigation: /port worked the 4-candidate hypothesis list from SPRINT.md
;; cheapest-first. Candidates 1, 2, 4 (peers-includes-self, post-make-grid
;; state, peer-helper instrumentation) cleared without finding a defect.
;; Candidate 3 (eliminate match arms) was a partial hit: the `Given _` and
;; `Solved _` arms returned `(Some g)` unconditionally, silently allowing
;; two peers to hold the same value. That was a real algorithmic hole
;; (Layer 1). Applying the obvious fix (return None when v == d) regressed
;; every valid puzzle — propagation returned None where it should not
;; (Layer 2). Reduction produced a non-Sudoku repro at
;; `exemplar/repro-slice2.cl` — an inline ADT constructor wrapping a Vec,
;; passed as an argument, read a corrupt length on the callee side
;; (Layer 3).
;;
;; Resolution: Layer 3 is a consuming-convention RC bug in
;; `crates/cranelisp-backend/src/compiler/mod.rs::is_last_use` — borrowed
;; vars were eligible for last-use transfer. /backend closed it with a
;; 14-line gate; see `design/backend/ring2-rc.md §5.5` for the rule.
;; Layer 2 bundles into Layer 3 by construction (same RC path, different
;; caller shape). Layer 1 (the two-line eliminate fix) is applied in this
;; file — the `Given v` / `Solved v` arms now return `None` when `v == d`.
;;
;; Regression guards:
;;   - `tests/exemplar_solver_correctness.rs::eliminate_on_same_value_given_returns_none`
;;     (T-S2-1) — Layer 1 contract.
;;   - `tests/exemplar_solver_correctness.rs::inline_adt_arg_wrapping_vec_preserves_len`
;;     (T-S2-2) — Layer 3 minimal repro.
;;
;; Repro-file migration: `exemplar/repro-slice2.cl` and
;; `exemplar/test-eliminate-contract.cl` are pending relocation to the
;; `tests/` tree per user directive 2026-04-22 — tracked as Slice 5 I
;; (/qa Wave 5).

(defn test-easy-puzzle []
  (match (make-grid "003020600900305001001806400008102900700000008006708200002609500800203009005010300")
    [(Some g)
       (match (solve g)
         [(Success solution)
            (if (eq-i64 (count-determined solution) 81) None
              (Some "easy puzzle should be fully determined"))
          Unsolvable (Some "easy puzzle should be solvable")])
     None (Some "make-grid should accept the easy puzzle string")]))

(defn test-hard-puzzle []
  (match (make-grid "800000000003600000070090200050007000000045700000100030001000068008500010090000400")
    [(Some g)
       (match (solve g)
         [(Success solution)
            (if (eq-i64 (count-determined solution) 81) None
              (Some "hard puzzle should be fully determined"))
          Unsolvable (Some "hard puzzle should be solvable")])
     None (Some "make-grid should accept the hard puzzle string")]))

(defn test-unsolvable []
  (match (make-grid "550000000000000000000000000000000000000000000000000000000000000000000000000000000")
    [(Some g)
       (match (solve g)
         [(Success _) (Some "puzzle with two 5s in row 0 should be unsolvable")
          Unsolvable None])
     None (Some "make-grid should accept the malformed puzzle string")]))
