;; solver.cl — Sudoku constraint propagation and backtracking solver
;;
;; Implements:
;; - eliminate: remove a digit from a cell's candidates
;; - propagate: iterate constraint elimination to fixpoint
;; - find-min-candidates: MRV heuristic for backtracking
;; - solve: main solver combining propagation and backtracking
;;
;; Depends on: grid.cl (Cell, Grid, SolveResult, bitmask ops, peers)
;; Depends on: prelude (Option, traits, operators, macros)
;;
;; The solver logic itself uses only Int and Vec operations; string handling
;; (via grid.cl's make-grid char-at and the board formatters) is confined to
;; parsing/rendering.

(platform stdio)

;; Idiomatic surface (S86 de-leak): arithmetic/comparison via prelude trait
;; operators; Vec access via the curated `count`/`get`/`assoc`; the string +
;; IO primitives imported by name. Solver logic is pure Int/Vec; only `main`
;; and `build-output` touch strings and IO.
;;
;; S88 adoption (Stage D): heap-ADT (`Cell`) accumulators in the test grid
;; builders now use the curated `collections.vec/conj` (DEF-2 carve-out
;; retired — see grid.cl header). `digit-to-char` replaces the 10-arm
;; `digit-string` ladder.
(import [collections.vec [count get assoc conj]])
(import [primitives [char-at str-concat str-len not bind Pure]])
(import [text.string [digit-to-char]])

(import [grid [Grid Cell Given Solved Candidates SolveResult Success Unsolvable
               full-mask bit-set? bit-clear bit-count bit-lowest
               cell-at set-cell peers is-solved cell-determined? cell-value make-grid]])
(import [platform.stdio [print]])

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
      [(Given v)  (if (= v d) None (Some g))
       (Solved v) (if (= v d) None (Some g))
       (Candidates mask)
         (if (not (bit-set? mask d))
           ;; Digit not in candidates, no change
           (Some g)
           (let [new-mask (bit-clear mask d)]
             (if (= new-mask 0)
               ;; Contradiction: no candidates left
               None
               (if (= (bit-count new-mask) 1)
                 ;; Determined: exactly one candidate remains
                 (Some (set-cell g idx (Solved (bit-lowest new-mask))))
                 ;; Reduced: still multiple candidates
                 (Some (set-cell g idx (Candidates new-mask)))))))])))

;; Eliminate a digit from all peers of a given cell.
;; Used when a cell becomes determined (Given or Solved with value d).
;; Returns (Some grid) on success, None if any elimination causes contradiction.
(defn eliminate-from-peers-helper [g peer-list d i]
  (if (= i (count peer-list)) (Some g)
    (let [peer-idx (get peer-list i)]
      (match (eliminate g peer-idx d)
        [None None
         (Some g2) (eliminate-from-peers-helper g2 peer-list d (+ i 1))]))))

(defn eliminate-from-peers [g idx d]
  (eliminate-from-peers-helper g (peers idx) d 0))

;; Single pass of constraint propagation:
;; For every determined cell (Given or Solved), eliminate its value
;; from all peers' candidates.
;;
;; Returns (Some grid) with propagated constraints, or None on contradiction.
(defn propagate-pass-helper [g i]
  (if (= i 81) (Some g)
    (let [cell (cell-at g i)]
      (match cell
        [(Given v)
           (match (eliminate-from-peers g i v)
             [None None
              (Some g2) (propagate-pass-helper g2 (+ i 1))])
         (Solved v)
           (match (eliminate-from-peers g i v)
             [None None
              (Some g2) (propagate-pass-helper g2 (+ i 1))])
         (Candidates _)
           (propagate-pass-helper g (+ i 1))]))))

;; Check if any cell was changed during propagation by comparing
;; candidate masks. Returns true if grids differ.
(defn grids-differ-helper [g1 g2 i]
  (if (= i 81) false
    (let [c1 (cell-at g1 i)
          c2 (cell-at g2 i)]
      ;; Compare cells: if both are Candidates, compare masks
      (match c1
        [(Candidates m1)
           (match c2
             [(Candidates m2) (if (= m1 m2)
                                (grids-differ-helper g1 g2 (+ i 1))
                                true)
              _ true])
         (Given _)
           (match c2
             [(Given _) (grids-differ-helper g1 g2 (+ i 1))
              _ true])
         (Solved _)
           (match c2
             [(Solved _) (grids-differ-helper g1 g2 (+ i 1))
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
  (if (= i 81)
    (if (= best-idx -1) None (Some best-idx))
    (let [cell (cell-at g i)]
      (match cell
        [(Candidates mask)
           (let [cnt (bit-count mask)]
             (if (if (= best-idx -1) true (< cnt best-count))
               (find-min-helper g (+ i 1) i cnt)
               (find-min-helper g (+ i 1) best-idx best-count)))
         (Given _) (find-min-helper g (+ i 1) best-idx best-count)
         (Solved _) (find-min-helper g (+ i 1) best-idx best-count)]))))

(defn find-min-candidates [g]
  (find-min-helper g 0 -1 10))

;; ── Backtracking Solver ────────────────────────────────────────────────

;; Try each digit d from lo to 9 at the given cell index.
;; Returns the first successful solution or Unsolvable.
(defn try-digits [g idx mask d]
  (if (> d 9) Unsolvable
    (if (not (bit-set? mask d))
      ;; Digit not a candidate, skip
      (try-digits g idx mask (+ d 1))
      ;; Try setting this cell to d and solving
      (let [g2 (set-cell g idx (Solved d))]
        (match (solve g2)
          [(Success solution) (Success solution)
           Unsolvable (try-digits g idx mask (+ d 1))])))))

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
;; S88 G6 adoption: the 10-arm `if` ladder is replaced by the stdlib
;; `text.string/digit-to-char` (inverse of grid's char parsing); 0 maps to
;; the board's blank glyph ".".
(defn digit-string [v]
  (if (= v 0) "." (digit-to-char v)))

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
    (if (= ch "0") "." ch)))

(defn format-row-from-str [s row col acc]
  (if (= col 9) acc
    (let [idx (+ (* row 9) col)
          ch (format-cell-char s idx)
          sep (if (= col 0) ""
                (if (if (= col 3) true (= col 6))
                  " | "
                  " "))]
      (format-row-from-str s row (+ col 1) (str-concat acc (str-concat sep ch))))))

(defn format-board-from-str [s row acc]
  (if (= row 9) acc
    (let [row-str (format-row-from-str s row 0 "")
          sep (if (= row 0) ""
                (if (if (= row 3) true (= row 6))
                  "\n------+-------+------\n"
                  "\n"))]
      (format-board-from-str s (+ row 1) (str-concat acc (str-concat sep row-str))))))

(defn format-board-str [s]
  (format-board-from-str s 0 ""))

;; Format a solved Grid as a board string.
;; Extracts cell values and builds the display.
(defn format-row-helper [g r col acc]
  (if (= col 9) acc
    (let [idx (+ (* r 9) col)
          v (cell-value (cell-at g idx))
          ds (digit-string v)
          sep (if (= col 0) ""
                (if (if (= col 3) true (= col 6))
                  " | "
                  " "))]
      (format-row-helper g r (+ col 1) (str-concat acc (str-concat sep ds))))))

(defn format-row [g r]
  (format-row-helper g r 0 ""))

(defn format-board-helper [g r acc]
  (if (= r 9) acc
    (let [row-str (format-row g r)
          sep (if (= r 0) ""
                (if (if (= r 3) true (= r 6))
                  "\n------+-------+------\n"
                  "\n"))]
      (format-board-helper g (+ r 1) (str-concat acc (str-concat sep row-str))))))

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

;; Main: solve a hard-coded puzzle and print the input board followed by the
;; full solution. The whole 81-cell grid solves end-to-end (exit 0, valid
;; solution); the earlier deep-recursion segfault is resolved. For the full
;; story (parse-form-body → make-grid → solve → ASCII + HTML render) see the
;; headline entry in `user.cl`.
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
  (if (= i 81) acc
    (if (cell-determined? (cell-at g i))
      (count-determined-helper g (+ i 1) (+ acc 1))
      (count-determined-helper g (+ i 1) acc))))

(defn count-determined [g]
  (count-determined-helper g 0 0))

;; --- Test grid builders (no `let`-defined `build` recursion) ---

;; Build a grid: cell 0 has the given mask as Candidates, the rest are Given 1.
(defn build-mask-then-givens-helper [v i mask]
  (if (= i 81) v
    (if (= i 0)
      (build-mask-then-givens-helper (conj v (Candidates mask)) (+ i 1) mask)
      (build-mask-then-givens-helper (conj v (Given 1)) (+ i 1) mask))))

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
           [(Solved v) (if (= v 3) None
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
;; Slice 2 + Slice 4 closure 2026-04-22 — three-layer Sudoku correctness
;; defect, fully resolved in Sprint 61.
;;
;;   Layer 1 — algorithmic hole in `eliminate` (landed Wave 2). The
;;     `(Given v)` / `(Solved v)` match arms returned `(Some g)`
;;     unconditionally, silently allowing two peers to hold the same value.
;;     Fix: return `None` when `v == d` (applied above in this file).
;;
;;   Layer 2 — Sudoku backtracking regression unmasked by the Layer 1 fix
;;     (resolved Wave 3). Root cause: H6 `ensure_module_exists` atomicity
;;     race in `crates/cranelisp-typecheck/src/checker.rs` — concurrent
;;     module registration could skip the publish step, leaving the
;;     backtracker with a torn module view. Fix: atomic
;;     check-then-create-then-publish transaction. See
;;     `design/int/heisenbug-race-closure.md`.
;;
;;   Layer 3 — inline-ADT-arg-wrapping-Vec codegen bug (resolved Wave 4).
;;     An inline ADT constructor holding a Vec, passed as a function
;;     argument, read a corrupt length on the callee side because the
;;     captured inner Vec was freed before the callee returned. Fix:
;;     H(4-1'') `emit_capture_return_inc` codegen helper. See
;;     `design/backend/slice-4-21-hello-io-investigation.md` and
;;     `design/backend/ring2-rc.md §5.6`.
;;
;; Regression guards (inline repros, no exemplar dependency):
;;   - `tests/exemplar_solver_correctness.rs::eliminate_on_same_value_given_returns_none`
;;     (T-S2-1) — Layer 1 contract.
;;   - `tests/exemplar_solver_correctness.rs::inline_adt_arg_wrapping_vec_preserves_len`
;;     (T-S2-2) — Layer 3 minimal repro.
;;
;; Repro-handoff migration (Slice 5 I, Wave 5): the two `.cl` repro files
;; that previously lived in `exemplar/` (`repro-slice2.cl`,
;; `test-eliminate-contract.cl`) have been inlined into the Rust
;; regression tests above per `memory/feedback_repro_handoff.md` and
;; deleted from `exemplar/`. Compiler regression guards no longer
;; depend on the showcase tree.
;;
;; Pre-existing issue (unresolved, carried):
;;   - Full 81-cell solve stack-overflows in deep recursive Grid/Vec
;;     copying. Ledgered in `tests/plan/baseline.md`; target S62. The
;;     IO and formatting path works end-to-end; only the inner solve
;;     recursion is affected.

(defn test-easy-puzzle []
  (match (make-grid "003020600900305001001806400008102900700000008006708200002609500800203009005010300")
    [(Some g)
       (match (solve g)
         [(Success solution)
            (if (= (count-determined solution) 81) None
              (Some "easy puzzle should be fully determined"))
          Unsolvable (Some "easy puzzle should be solvable")])
     None (Some "make-grid should accept the easy puzzle string")]))

(defn test-hard-puzzle []
  (match (make-grid "800000000003600000070090200050007000000045700000100030001000068008500010090000400")
    [(Some g)
       (match (solve g)
         [(Success solution)
            (if (= (count-determined solution) 81) None
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
