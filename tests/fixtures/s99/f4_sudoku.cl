;; f4_sudoku.cl — Sprint 99 Wave 0.3 fixture F4: the confounded reference.
;;
;; A real (backtracking-requiring) 9x9 Sudoku solve on the nested-ADT grid — a
;; free-standing port of exemplar/{grid,solver}.cl with ZERO stdlib dependency
;; (bit ops via the native primitives bit-and/bit-or/bit-not/shl/popcount; Vec
;; via bare vec-get/vec-set/vec-push; Option/SolveResult defined inline).
;;
;; Purpose: the confounded reference kept ONLY to reconcile F1–F3 against the
;; observed "~10× slower than serial". It combines every term at once — machinery
;; (F1), copy/alloc/RC contention (F2, via `set-cell` copy-per-guess), and the
;; speculative first-success search shape (F3). Its lenient-vs-serial ratio is
;; the number the sprint set out to decompose.
;;
;; The parallel (speculative) search returns the SAME grid a serial search does
;; (unique solution, pure branches) — so the exit code (a checksum of the solved
;; grid) MUST be identical under default and CRANELISP_NO_LENIENT=1. That is the
;; committed parallel≡serial correctness guard.
;;
;; Free-standing: bare primitives only, no stdlib, no prelude.

(import [primitives [*]])

;; ── Data types ──────────────────────────────────────────────────────────
;; `Option` (None/Some) is SEEDED by `primitives` (src/bootstrap.rs step 4) and
;; already reached via the `(import [primitives [*]])` glob above — reuse THE
;; canonical `primitives/Option` (§3.8.4 nominal typing) rather than REdefining
;; a second, distinct ADT (which would author a define-over-glob-import
;; collision forbidden by §8.6.4). Cell/Grid/SolveResult are this fixture's own.
(deftype Cell (Given [:Int given-value]) (Solved [:Int solved-value]) (Candidates [:Int bitmask]))
(deftype Grid [cells])
(deftype SolveResult (Success [grid]) Unsolvable)

;; ── Arithmetic / bit helpers (native primitives) ────────────────────────
(defn rem-i64 [a b] (sub-i64 a (mul-i64 (div-i64 a b) b)))
(defn full-mask [] 511)
(defn bit-set? [mask d] (not (eq-i64 (bit-and mask (shl 1 (sub-i64 d 1))) 0)))
(defn bit-clear [mask d] (bit-and mask (bit-not (shl 1 (sub-i64 d 1)))))
(defn bit-count [mask] (popcount mask))
(defn bit-lowest-helper [mask d]
  (if (gt-i64 d 9) 0 (if (bit-set? mask d) d (bit-lowest-helper mask (add-i64 d 1)))))
(defn bit-lowest [mask] (bit-lowest-helper mask 1))

;; ── Grid index helpers ──────────────────────────────────────────────────
(defn row-of [idx] (div-i64 idx 9))
(defn col-of [idx] (rem-i64 idx 9))
(defn box-of [idx] (add-i64 (mul-i64 (div-i64 (row-of idx) 3) 3) (div-i64 (col-of idx) 3)))

;; ── Grid accessors ──────────────────────────────────────────────────────
(defn cell-at [g idx] (match g [(Grid cells) (vec-get cells idx)]))
(defn set-cell [g idx c] (match g [(Grid cells) (Grid (vec-set cells idx c))]))
(defn cell-value [c] (match c [(Given v) v  (Solved v) v  (Candidates _) 0]))

;; ── Peers ───────────────────────────────────────────────────────────────
(defn peers-helper [idx i acc]
  (if (eq-i64 i 81) acc
    (if (eq-i64 i idx)
      (peers-helper idx (add-i64 i 1) acc)
      (if (if (eq-i64 (row-of i) (row-of idx)) true
            (if (eq-i64 (col-of i) (col-of idx)) true
              (eq-i64 (box-of i) (box-of idx))))
        (peers-helper idx (add-i64 i 1) (vec-push acc i))
        (peers-helper idx (add-i64 i 1) acc)))))
(defn peers [idx] (peers-helper idx 0 []))

;; ── Grid construction (string parse) ────────────────────────────────────
(defn make-grid-helper [s i cells]
  (if (eq-i64 i 81) (Some (Grid cells))
    (let [ch (char-at s i)]
      (if (str-eq ch ".") (make-grid-helper s (add-i64 i 1) (vec-push cells (Candidates (full-mask))))
      (if (str-eq ch "1") (make-grid-helper s (add-i64 i 1) (vec-push cells (Given 1)))
      (if (str-eq ch "2") (make-grid-helper s (add-i64 i 1) (vec-push cells (Given 2)))
      (if (str-eq ch "3") (make-grid-helper s (add-i64 i 1) (vec-push cells (Given 3)))
      (if (str-eq ch "4") (make-grid-helper s (add-i64 i 1) (vec-push cells (Given 4)))
      (if (str-eq ch "5") (make-grid-helper s (add-i64 i 1) (vec-push cells (Given 5)))
      (if (str-eq ch "6") (make-grid-helper s (add-i64 i 1) (vec-push cells (Given 6)))
      (if (str-eq ch "7") (make-grid-helper s (add-i64 i 1) (vec-push cells (Given 7)))
      (if (str-eq ch "8") (make-grid-helper s (add-i64 i 1) (vec-push cells (Given 8)))
      (if (str-eq ch "9") (make-grid-helper s (add-i64 i 1) (vec-push cells (Given 9)))
      (if (str-eq ch "0") (make-grid-helper s (add-i64 i 1) (vec-push cells (Candidates (full-mask))))
        None))))))))))))))
(defn make-grid [s]
  (if (eq-i64 (str-len s) 81) (make-grid-helper s 0 []) None))

;; ── is-solved ───────────────────────────────────────────────────────────
(defn is-solved-helper [g i]
  (if (eq-i64 i 81) true
    (match (cell-at g i)
      [(Given _) (is-solved-helper g (add-i64 i 1))
       (Solved _) (is-solved-helper g (add-i64 i 1))
       (Candidates _) false])))
(defn is-solved [g] (is-solved-helper g 0))

;; ── Constraint propagation ──────────────────────────────────────────────
(defn eliminate [g idx d]
  (let [cell (cell-at g idx)]
    (match cell
      [(Given v)  (if (eq-i64 v d) None (Some g))
       (Solved v) (if (eq-i64 v d) None (Some g))
       (Candidates mask)
         (if (not (bit-set? mask d))
           (Some g)
           (let [new-mask (bit-clear mask d)]
             (if (eq-i64 new-mask 0)
               None
               (if (eq-i64 (bit-count new-mask) 1)
                 (Some (set-cell g idx (Solved (bit-lowest new-mask))))
                 (Some (set-cell g idx (Candidates new-mask)))))))])))

(defn eliminate-from-peers-helper [g peer-list d i]
  (if (eq-i64 i (vec-len peer-list)) (Some g)
    (let [peer-idx (vec-get peer-list i)]
      (match (eliminate g peer-idx d)
        [None None
         (Some g2) (eliminate-from-peers-helper g2 peer-list d (add-i64 i 1))]))))
(defn eliminate-from-peers [g idx d] (eliminate-from-peers-helper g (peers idx) d 0))

(defn propagate-pass-helper [g i]
  (if (eq-i64 i 81) (Some g)
    (let [cell (cell-at g i)]
      (match cell
        [(Given v)
           (match (eliminate-from-peers g i v)
             [None None  (Some g2) (propagate-pass-helper g2 (add-i64 i 1))])
         (Solved v)
           (match (eliminate-from-peers g i v)
             [None None  (Some g2) (propagate-pass-helper g2 (add-i64 i 1))])
         (Candidates _) (propagate-pass-helper g (add-i64 i 1))]))))

(defn grids-differ-helper [g1 g2 i]
  (if (eq-i64 i 81) false
    (let [c1 (cell-at g1 i)  c2 (cell-at g2 i)]
      (match c1
        [(Candidates m1)
           (match c2
             [(Candidates m2) (if (eq-i64 m1 m2) (grids-differ-helper g1 g2 (add-i64 i 1)) true)
              _ true])
         (Given _)
           (match c2 [(Given _) (grids-differ-helper g1 g2 (add-i64 i 1))  _ true])
         (Solved _)
           (match c2 [(Solved _) (grids-differ-helper g1 g2 (add-i64 i 1))  _ true])]))))

(defn propagate [g]
  (match (propagate-pass-helper g 0)
    [None None
     (Some g2)
       (if (grids-differ-helper g g2 0) (propagate g2) (Some g2))]))

;; ── MRV heuristic ───────────────────────────────────────────────────────
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
(defn find-min-candidates [g] (find-min-helper g 0 -1 10))

;; ── Parallel backtracking search ────────────────────────────────────────
(defn mask-to-digits-helper [mask d acc]
  (if (gt-i64 d 9) acc
    (if (bit-set? mask d)
      (mask-to-digits-helper mask (add-i64 d 1) (vec-push acc d))
      (mask-to-digits-helper mask (add-i64 d 1) acc))))
(defn mask-to-digits [mask] (mask-to-digits-helper mask 1 []))

(defn first-success [a b] (match a [(Success s) (Success s)  _ b]))

(defn mid-of [lo hi] (add-i64 lo (div-i64 (sub-i64 hi lo) 2)))

;; Copy-free index-range D&C over the candidate digits. The two recursive
;; solve-range calls are the independent apply-args of first-success and
;; auto-spark (lenient eval) — the search tree parallelises with no `spark` in
;; the source. Speculative: every branch is evaluated; losers are discarded.
(defn solve-range [g idx digits lo hi]
  (if (le-i64 (sub-i64 hi lo) 1)
    (solve (set-cell g idx (Solved (vec-get digits lo))))
    (first-success
      (solve-range g idx digits lo (mid-of lo hi))
      (solve-range g idx digits (mid-of lo hi) hi))))

(defn solve [g]
  (match (propagate g)
    [None Unsolvable
     (Some g2)
       (if (is-solved g2)
         (Success g2)
         (match (find-min-candidates g2)
           [None Unsolvable
            (Some idx)
              (let [cell (cell-at g2 idx)]
                (match cell
                  [(Candidates mask)
                     (let [digits (mask-to-digits mask)]
                       (if (eq-i64 (vec-len digits) 0)
                         Unsolvable
                         (solve-range g2 idx digits 0 (vec-len digits))))
                   _ Unsolvable]))]))]))

;; ── Checksum (correctness witness: identical under serial and parallel) ──
(defn checksum-helper [g i acc]
  (if (eq-i64 i 81) acc
    (checksum-helper g (add-i64 i 1) (add-i64 acc (cell-value (cell-at g i))))))
(defn checksum [g] (checksum-helper g 0 0))

;; COMMITTED puzzle: an ALREADY-SOLVED grid (0 blanks) so the committed
;; parallel≡serial correctness guard runs fast under the DEBUG binary — it
;; exercises the full make-grid / propagate / is-solved / checksum pipeline and
;; all the nested-ADT/Vec machinery, but never reaches the backtracking search
;; (whose contention is exactly what makes parallel slow). The measurement
;; harness (tests/perf/s99_measure.py) substitutes a propagation-dominated
;; (EASY) and a genuinely-hard backtracking (HARD) puzzle for the timing sweep —
;; that is where the speculative par-map-reduce search path and the contention
;; actually run. F2/F3 carry the committed parallel≡serial guard for the
;; spark/search path itself.
(defn main []
  (match (make-grid "483921657967345821251876493548132976729564138136798245372689514814253769695417382")
    [None (Pure 0)
     (Some g)
       (match (solve g)
         [(Success solution) (Pure (rem-i64 (checksum solution) 251))
          Unsolvable (Pure 0)])]))
