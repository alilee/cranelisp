;; solver.cl — Sudoku constraint propagation and backtracking solver
;;
;; Implements:
;; - eliminate: remove a digit from a cell's candidates
;; - propagate: iterate constraint elimination to fixpoint
;; - find-min-candidates: MRV heuristic for backtracking
;; - solve: main solver combining propagation and backtracking
;;
;; The solver uses only Int and Vec operations; strings appear only in the board
;; formatters. No result type here contains `IO`, and the module declares no
;; platform, since only an entry may declare one (spec/10-io.md §10.9.1).

(import [collections.vec [count get conj range vec-map vec-reduce]])
(import [collections.parallel [par-map-reduce]])
(import [primitives [char-at str-concat not]])
(import [text.string [digit-to-char]])
(import [testing.assertions [assert-eq assert-false]])

(import [grid [Grid Given Solved Candidates Success Unsolvable
               full-mask bit-set? bit-clear bit-count bit-lowest
               cell-at set-cell peers is-solved cell-value make-grid]])

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

;; ── Parallel Backtracking Search (lenient-eval showcase) ────────────────
;;
;; The backtracking search is, at heart, a **map-reduce over the candidate
;; digits** of the chosen cell:
;;
;;   - MAP   each candidate digit `d` to the result of committing `d` and
;;           recursively solving the resulting grid — `(solve (set-cell …))`;
;;   - REDUCE the per-digit results with `first-success`, an associative
;;           combiner (identity `Unsolvable`) that takes the first branch that
;;           solved.
;;
;; The branches are independent CPU computations, so the search uses
;; `collections.parallel/par-map-reduce`. It binds the two halves of the digit
;; Vec to independent `let` bindings, which lenient evaluation sparks onto the
;; thread pool; the spark budget runs an over-budget branch inline
;; (`design/backend/lenient-eval.md` §2.1, §3.6). The source has no `spark`,
;; `par` or threads.
;;
;; The search is speculative: every branch is evaluated and the losers are
;; discarded. The result does not depend on evaluation order, so
;; `CRANELISP_NO_LENIENT=1` gives the same solution. Parallel search is not
;; yet faster than serial (plan-exemplar.md, "Copy-per-guess performance").

;; Enumerate the set digits (1-9) of a candidate mask into a (Vec Int), using
;; the digit-domain `bit-set?` adapter. This is the collection `par-map-reduce`
;; maps the per-digit solve over.
(defn mask-to-digits-helper [mask d acc]
  (if (> d 9) acc
    (if (bit-set? mask d)
      (mask-to-digits-helper mask (+ d 1) (conj acc d))
      (mask-to-digits-helper mask (+ d 1) acc))))

(defn mask-to-digits [mask]
  (mask-to-digits-helper mask 1 []))

;; The associative reduce combiner: pick the first branch that solved, else the
;; second. Identity is `Unsolvable` (a two-sided identity: it never wins over a
;; Success, and `first-success Unsolvable b == b`). Correct even when `b` was
;; computed speculatively: a branch performs no IO, so the loser is discarded.
(defn first-success [a b]
  (match a
    [(Success s) (Success s)
     _ b]))

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
                  [(Candidates mask)
                     ;; Guess: parallel map-reduce over the candidate digits —
                     ;; map each digit to its recursive solve, reduce the
                     ;; results with `first-success` (identity `Unsolvable`).
                     ;; `par-map-reduce`'s independent halves spark the per-digit
                     ;; subtrees onto the thread pool (no `spark` in the source).
                     (let [digits (mask-to-digits mask)]
                       (if (= (count digits) 0)
                         Unsolvable
                         (par-map-reduce
                           (fn [d] (solve (set-cell g2 idx (Solved d))))
                           first-success
                           Unsolvable
                           digits)))
                   _ Unsolvable]))]))]))

;; ── Board Formatting ──────────────────────────────────────────────────
;;
;; A board prints one row per line, with a rule between the 3×3 boxes:
;;   d d d | d d d | d d d
;;   ...
;;   ------+-------+------

;; The text to put before column or row `i`: none before the first, `boundary`
;; before the fourth and seventh, `plain` otherwise.
(defn board-separator [i plain boundary]
  (if (= i 0) ""
    (if (if (= i 3) true (= i 6)) boundary plain)))

(defn column-separator [col] (board-separator col " " " | "))

(defn row-separator [row] (board-separator row "\n" "\n------+-------+------\n"))

;; Convert a cell value (1-9) to its string digit, or "." for 0.
(defn digit-string [v]
  (if (= v 0) "." (digit-to-char v)))

;; One puzzle-string character for display: `0` shows as `.`.
(defn format-cell-char [s i]
  (let [ch (char-at s i)]
    (if (= ch "0") "." ch)))

;; Lay out `(cell-text idx)` for the 81 indices as a board.
(defn format-board-with [cell-text]
  (vec-reduce
    (fn [board row]
      (str-concat board
        (str-concat (row-separator row)
          (vec-reduce
            (fn [line col]
              (str-concat line
                (str-concat (column-separator col) (cell-text (+ (* row 9) col)))))
            ""
            (range 0 9)))))
    ""
    (range 0 9)))

;; Format an 81-character puzzle string as a board.
(defn format-board-str [s]
  (format-board-with (fn [i] (format-cell-char s i))))

;; Format a Grid as a board; an undetermined cell shows as `.`.
(defn format-board [g]
  (format-board-with (fn [i] (digit-string (cell-value (cell-at g i))))))

;; ── Tests ───────────────────────────────────────────────────────────────
;;
;; Each `test-*` returns `(Option String)`, `None` for a pass
;; (repl/spec/16-test-discovery.md §16.1). `tests.cl` calls them, and
;; `cranelisp --test` discovers them.

;; --- Elimination tests ---

;; Cell 0 holds `mask` as Candidates; the rest are Given 1.
(defn make-test-grid-with-mask [mask]
  (Grid (vec-map (fn [i] (if (= i 0) (Candidates mask) (Given 1))) (range 0 81))))

;; Eliminate `d` at `idx` of the test grid whose cell 0 holds `mask`, and show
;; the resulting cell, or "contradiction".
(defn eliminated-cell [mask idx d]
  (match (eliminate (make-test-grid-with-mask mask) idx d)
    [None "contradiction"
     (Some g) (show (cell-at g idx))]))

(defn test-eliminate-removes-digit []
  (assert-eq "Candidates 495" (eliminated-cell (full-mask) 0 5)))

(defn test-eliminate-no-effect-on-given []
  (assert-eq "Given 1" (eliminated-cell (full-mask) 1 5)))

;; {3, 7} is the mask 4 + 64 = 68.
(defn test-eliminate-determines-cell []
  (assert-eq "Solved 3" (eliminated-cell 68 0 7)))

;; {5} is the mask 16.
(defn test-eliminate-contradiction []
  (assert-eq "contradiction" (eliminated-cell 16 0 5)))

;; --- Solver tests ---
;;
;; `eliminate` returns `None` when a Given or Solved cell already holds the
;; eliminated digit, so two peers never hold the same value. The compiler's
;; regression guard for that contract is self-contained:
;; `tests/exemplar.rs::t_s2_1_eliminate_contract_on_given_returns_none`.

;; Flatten a solved grid to its bare 81-digit string (no separators).
(defn solution-digits [g]
  (vec-reduce
    (fn [acc i] (str-concat acc (digit-string (cell-value (cell-at g i)))))
    ""
    (range 0 81)))

;; Solve `puzzle` and return its 81 solution digits, or why it was not solved.
(defn solve-to-digits [puzzle]
  (match (make-grid puzzle)
    [None "make-grid rejected the puzzle"
     (Some g)
       (match (solve g)
         [(Success solution) (solution-digits solution)
          Unsolvable "unsolvable"])]))

;; The puzzle `user.cl` and `smoke.cl` print; propagation alone solves it.
(defn test-easy-puzzle []
  (assert-eq
    "483921657967345821251876493548132976729564138136798245372689514814253769695417382"
    (solve-to-digits
      "003020600900305001001806400008102900700000008006708200002609500800203009005010300")))

;; --- Parallel-search equivalence ---
;;
;; A valid Sudoku has one solution, so the parallel and serial searches must
;; return the same grid. `test-solve-parallel-equiv` pins the solution of a
;; puzzle that propagation alone does not solve, so the `par-map-reduce` path
;; runs; `tests.cl` passing in both modes is the parallel ≡ serial guard.

;; Propagation stalls on this puzzle.
(defn equiv-puzzle []
  "2...8.3...6..7..84.3.5..2.9...1.54.8.........4.27.6...3.1..7.4.72..4..6...4.1...3")

(defn test-equiv-puzzle-needs-search []
  (match (make-grid (equiv-puzzle))
    [None (Some "make-grid should accept the equivalence puzzle")
     (Some g)
       (match (propagate g)
         [None (Some "propagation should not contradict the equivalence puzzle")
          (Some g2) (assert-false (is-solved g2))])]))

(defn test-solve-parallel-equiv []
  (assert-eq
    "245981376169273584837564219976125438513498627482736951391657842728349165654812793"
    (solve-to-digits (equiv-puzzle))))

(defn test-hard-puzzle []
  (assert-eq
    "812753649943682175675491283154237896369845721287169534521974368438526917796318452"
    (solve-to-digits
      "800000000003600000070090200050007000000045700000100030001000068008500010090000400")))

;; Two 5s in row 0.
(defn test-unsolvable []
  (assert-eq "unsolvable"
    (solve-to-digits
      "550000000000000000000000000000000000000000000000000000000000000000000000000000000")))
