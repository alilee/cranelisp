;; grid.cl — Sudoku grid data types and operations
;;
;; Defines the core data model for a 9x9 Sudoku grid:
;; - Cell: Given (fixed digit), Solved (determined digit), or Candidates (bitmask)
;; - Grid: flat Vec of 81 Cells
;; - SolveResult: Success or Unsolvable
;; - PropResult: result of constraint propagation on a single cell
;;
;; Bitmask convention: digits 1-9 are represented as bits 0-8.
;; Digit d is set when bit (d-1) is set, i.e. mask has value (1 << (d-1)).
;; full-mask = 0x1FF = 511 = all 9 digits present.
;;
;; Depends on: prelude (Option, traits, macros)
;; Blocked by: F2 string primitives (char-at) for make-grid

(import [primitives [*]])

;; ── Data Types ──────────────────────────────────────────────────────────

(deftype Cell
  (Given [:Int value])
  (Solved [:Int value])
  (Candidates [:Int bitmask]))

(deftype Grid [cells])

(deftype SolveResult
  (Success [grid])
  Unsolvable)

(deftype PropResult
  Unchanged
  Reduced
  Determined
  Contradiction)

;; ── Constants ───────────────────────────────────────────────────────────

;; All 9 digits set: bits 0..8 = 0b111111111 = 511
;; Originally `(const full-mask 511)` — converted to a zero-arg function
;; because `const` expands to a compile-time bare-symbol macro that is
;; not visible as a value across module boundaries.
(defn full-mask [] 511)

;; ── Arithmetic helpers ──────────────────────────────────────────────────

;; Integer remainder: a mod b = a - b * (a / b)
;; Needed because there is no mod/rem primitive.
(defn rem-i64 [a b]
  (sub-i64 a (mul-i64 (div-i64 a b) b)))

;; ── Bitmask operations ─────────────────────────────────────────────────

;; Test if digit d (1-9) is set in bitmask.
;; Bit for digit d is at position (d-1).
;; We test by shifting mask right by (d-1) and checking the low bit.
;;
;; Since we don't have bitwise ops as primitives, we simulate:
;;   (mask >> n) is (div-i64 mask (2^n))
;;   (mask & 1)  is (rem-i64 mask 2)
;;   (1 << n)    is a power of 2
;;
;; Helper: compute 2^n for small n (0-8) via repeated multiplication.
(defn pow2 [n]
  (if (eq-i64 n 0) 1
    (mul-i64 2 (pow2 (sub-i64 n 1)))))

;; Test if digit d (1-9) is set in bitmask.
(defn bit-set? [mask d]
  (let [shift (sub-i64 d 1)
        p (pow2 shift)
        shifted (div-i64 mask p)]
    (eq-i64 (rem-i64 shifted 2) 1)))

;; Clear digit d (1-9) from bitmask.
;; If the bit is set, subtract 2^(d-1) from mask.
(defn bit-clear [mask d]
  (if (bit-set? mask d)
    (sub-i64 mask (pow2 (sub-i64 d 1)))
    mask))

;; Set digit d (1-9) in bitmask.
(defn bit-set [mask d]
  (if (bit-set? mask d)
    mask
    (add-i64 mask (pow2 (sub-i64 d 1)))))

;; Count number of set bits in a 9-bit mask (popcount).
;; Iterate digits 1-9, count those that are set.
(defn bit-count-helper [mask d acc]
  (if (gt-i64 d 9) acc
    (if (bit-set? mask d)
      (bit-count-helper mask (add-i64 d 1) (add-i64 acc 1))
      (bit-count-helper mask (add-i64 d 1) acc))))

(defn bit-count [mask]
  (bit-count-helper mask 1 0))

;; Return the lowest set digit (1-9) in a bitmask.
;; Returns 0 if mask is empty.
(defn bit-lowest-helper [mask d]
  (if (gt-i64 d 9) 0
    (if (bit-set? mask d) d
      (bit-lowest-helper mask (add-i64 d 1)))))

(defn bit-lowest [mask]
  (bit-lowest-helper mask 1))

;; ── Grid index helpers ─────────────────────────────────────────────────

;; Row index (0-8) from flat index (0-80).
(defn row-of [idx] (div-i64 idx 9))

;; Column index (0-8) from flat index (0-80).
(defn col-of [idx] (rem-i64 idx 9))

;; Box index (0-8) from flat index (0-80).
;; Box is a 3x3 region. Box row = row/3, box col = col/3.
;; Box index = box_row * 3 + box_col.
(defn box-of [idx]
  (let [r (row-of idx)
        c (col-of idx)]
    (add-i64 (mul-i64 (div-i64 r 3) 3) (div-i64 c 3))))

;; ── Grid accessors ─────────────────────────────────────────────────────

;; Access cell at flat index (0-80).
(defn cell-at [g idx]
  (match g [(Grid cells) (vec-get cells idx)]))

;; Functional update: return new grid with cell at idx replaced.
(defn set-cell [g idx c]
  (match g [(Grid cells) (Grid (vec-set cells idx c))]))

;; ── Peer calculation ───────────────────────────────────────────────────

;; Build list of all 20 peer indices for a given cell index.
;; Peers share the same row, column, or 3x3 box (excluding self).
;;
;; Strategy: iterate all 81 indices, collect those that share
;; row, column, or box with idx (but are not idx itself).
(defn peers-helper [idx i acc]
  (if (eq-i64 i 81) acc
    (if (eq-i64 i idx)
      (peers-helper idx (add-i64 i 1) acc)
      (if (if (eq-i64 (row-of i) (row-of idx)) true
            (if (eq-i64 (col-of i) (col-of idx)) true
              (eq-i64 (box-of i) (box-of idx))))
        (peers-helper idx (add-i64 i 1) (vec-push acc i))
        (peers-helper idx (add-i64 i 1) acc)))))

(defn peers [idx]
  (peers-helper idx 0 []))

;; ── Grid construction ──────────────────────────────────────────────────

;; Parse an 81-character string into a Grid.
;; Digits '1'-'9' become Given cells.
;; Dots '.' become Candidates with full-mask (all digits possible).
;; Returns None if the string is not exactly 81 characters,
;; or contains invalid characters.
;;
;; NOTE: This function depends on `char-at` (F2 string primitives).
;; `char-at` returns a 1-char String. We compare with str-eq.
(defn make-grid-helper [s i cells]
  (if (eq-i64 i 81) (Some (Grid cells))
    (let [ch (char-at s i)]
      (if (str-eq ch ".")
        (make-grid-helper s (add-i64 i 1) (vec-push cells (Candidates (full-mask))))
        ;; Try to parse as a digit 1-9.
        ;; We compare the character against digit strings.
        (if (str-eq ch "1") (make-grid-helper s (add-i64 i 1) (vec-push cells (Given 1)))
        (if (str-eq ch "2") (make-grid-helper s (add-i64 i 1) (vec-push cells (Given 2)))
        (if (str-eq ch "3") (make-grid-helper s (add-i64 i 1) (vec-push cells (Given 3)))
        (if (str-eq ch "4") (make-grid-helper s (add-i64 i 1) (vec-push cells (Given 4)))
        (if (str-eq ch "5") (make-grid-helper s (add-i64 i 1) (vec-push cells (Given 5)))
        (if (str-eq ch "6") (make-grid-helper s (add-i64 i 1) (vec-push cells (Given 6)))
        (if (str-eq ch "7") (make-grid-helper s (add-i64 i 1) (vec-push cells (Given 7)))
        (if (str-eq ch "8") (make-grid-helper s (add-i64 i 1) (vec-push cells (Given 8)))
        (if (str-eq ch "9") (make-grid-helper s (add-i64 i 1) (vec-push cells (Given 9)))
        ;; '0' treated as empty (like '.')
        (if (str-eq ch "0") (make-grid-helper s (add-i64 i 1) (vec-push cells (Candidates (full-mask))))
          None))))))))))))))

(defn make-grid [s]
  (if (eq-i64 (str-len s) 81)
    (make-grid-helper s 0 [])
    None))

;; ── Grid solved check ──────────────────────────────────────────────────

;; Check if all cells are determined (Given or Solved).
(defn is-solved-helper [g i]
  (if (eq-i64 i 81) true
    (match (cell-at g i)
      [(Given _) (is-solved-helper g (add-i64 i 1))
       (Solved _) (is-solved-helper g (add-i64 i 1))
       (Candidates _) false])))

(defn is-solved [g]
  (is-solved-helper g 0))

;; ── Cell value extraction ──────────────────────────────────────────────

;; Get the determined value of a cell, or 0 if it's a Candidates cell.
(defn cell-value [c]
  (match c
    [(Given v) v
     (Solved v) v
     (Candidates _) 0]))

;; Check if a cell is determined (Given or Solved).
(defn cell-determined? [c]
  (match c
    [(Given _) true
     (Solved _) true
     (Candidates _) false]))

;; ── Tests ───────────────────────────────────────────────────────────────
;; FIXME(/int): test submodules disabled — parent↔child typecheck deadlock
;; (spec §8.3.7 + Decision 30). Inline (mod test ...) forms using
;; (import [super [*]]) block forever against the current form-by-form
;; scheduler. Re-enable once the scheduler supports sibling super-import
;; or the exemplar tests are migrated to discover-tests / run-test.
;; See: tests/wave6_port.md (TODO) and spec/08-modules.md §8.3.7.
