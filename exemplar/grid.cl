;; grid.cl — Sudoku grid data types and operations.
;;
;; - Cell: Given (fixed digit), Solved (determined digit), or Candidates (bitmask)
;; - Grid: flat Vec of 81 Cells
;; - SolveResult: Success or Unsolvable
;;
;; Candidates are a 9-bit mask: digit d (1-9) is bit d-1, and `full-mask` (511)
;; holds all nine. The digit-domain bit verbs below adapt the bit-position verbs
;; of `num.bits`; the masks never use the sign bit of its 64-bit operations.
;;
;; `peers`, `make-grid` and `is-solved` are each one multi-signature `defn`
;; whose short clause seeds the accumulator of the long one (spec §5.1.2).

(import [collections.vec [count get assoc conj range vec-map]])
(import [primitives [char-at str-len str-concat]])
(import [text.string [char-to-digit]])
;; `num.bits/bit-clear` and `bit-set` are not imported: grid defines
;; digit-domain verbs of the same names.
(import [num.bits [bit-shift-left bit-test bit-and bit-or bit-not popcount]])
(import [testing.assertions [check assert-eq assert-true assert-false]])

;; ── Data Types ──────────────────────────────────────────────────────────

(deftype Cell
  (Given [:Int given-value])
  (Solved [:Int solved-value])
  (Candidates [:Int bitmask]))

(deftype (Grid cells-type) [:cells-type cells])

(deftype (SolveResult grid-type)
  (Success [:grid-type grid])
  Unsolvable)

;; ── Constants ───────────────────────────────────────────────────────────

;; All 9 digits set: bits 0..8 = 0b111111111 = 511
(defn full-mask [] 511)

;; ── Arithmetic helpers ──────────────────────────────────────────────────

;; Integer remainder: a - b * (a / b). Same as `num.int/rem`; kept local
;; (plan-exemplar.md, "`rem-i64` stays inline").
(defn rem-i64 [a b]
  (- a (* (/ a b) b)))

;; ── Bitmask operations (digit-domain adapters over num.bits) ────────────

;; 2^n — single set bit at position n.
(defn pow2 [n] (bit-shift-left 1 n))

;; Test if digit d (1-9) is set in bitmask.
(defn bit-set? [mask d]
  (bit-test mask (- d 1)))

;; Clear digit d (1-9) from bitmask.
(defn bit-clear [mask d]
  (bit-and mask (bit-not (bit-shift-left 1 (- d 1)))))

;; Set digit d (1-9) in bitmask.
(defn bit-set [mask d]
  (bit-or mask (bit-shift-left 1 (- d 1))))

;; Count number of set bits in the 9-bit mask (popcount).
(defn bit-count [mask]
  (popcount mask))

;; Return the lowest set digit (1-9) in a bitmask. Returns 0 if mask is empty.
(defn bit-lowest-helper [mask d]
  (if (> d 9) 0
    (if (bit-set? mask d) d
      (bit-lowest-helper mask (+ d 1)))))

(defn bit-lowest [mask]
  (bit-lowest-helper mask 1))

;; ── Grid index helpers ─────────────────────────────────────────────────

;; Row index (0-8) from flat index (0-80).
(defn row-of [idx] (/ idx 9))

;; Column index (0-8) from flat index (0-80).
(defn col-of [idx] (rem-i64 idx 9))

;; Box index (0-8) from flat index (0-80).
;; Box is a 3x3 region. Box row = row/3, box col = col/3.
;; Box index = box_row * 3 + box_col.
(defn box-of [idx]
  (let [r (row-of idx)
        c (col-of idx)]
    (+ (* (/ r 3) 3) (/ c 3))))

;; ── Grid accessors ─────────────────────────────────────────────────────

;; Access cell at flat index (0-80).
(defn cell-at [g idx]
  (match g [(Grid cells) (get cells idx)]))

;; Functional update: return new grid with cell at idx replaced.
(defn set-cell [g idx c]
  (match g [(Grid cells) (Grid (assoc cells idx c))]))

;; ── Peer calculation ───────────────────────────────────────────────────

;; The indices of the 20 cells sharing a row, column or box with `idx`.
(defn peers
  ([idx] (peers idx 0 []))
  ([idx i acc]
   (if (= i 81) acc
     (if (= i idx)
       (peers idx (+ i 1) acc)
       (if (if (= (row-of i) (row-of idx)) true
             (if (= (col-of i) (col-of idx)) true
               (= (box-of i) (box-of idx))))
         (peers idx (+ i 1) (conj acc i))
         (peers idx (+ i 1) acc))))))

;; ── Grid construction ──────────────────────────────────────────────────

;; One puzzle character as a cell: `.` and `0` are empty, `1`–`9` are givens,
;; and anything else is invalid.
(defn parse-cell [ch]
  (let [d (char-to-digit ch)]
    (cond
      (= ch ".") (Some (Candidates (full-mask)))
      (= d 0) (Some (Candidates (full-mask)))
      (> d 0) (Some (Given d))
      None)))

;; Parse an 81-character puzzle string into a Grid, or None if its length or
;; any character is invalid.
(defn make-grid
  ([s]
   (if (= (str-len s) 81)
     (make-grid s 0 [])
     None))
  ([s i cells]
   (if (= i 81) (Some (Grid cells))
     (match (parse-cell (char-at s i))
       [None None
        (Some c) (make-grid s (+ i 1) (conj cells c))]))))

;; ── Grid solved check ──────────────────────────────────────────────────

;; Check if all cells are determined (Given or Solved).
(defn is-solved
  ([g] (is-solved g 0))
  ([g i]
   (if (= i 81) true
     (match (cell-at g i)
       [(Given _) (is-solved g (+ i 1))
        (Solved _) (is-solved g (+ i 1))
        (Candidates _) false]))))

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

;; ── Display Cell ─────────────────────────────────────────────────────────
;; Renders a Cell at the REPL, in debug output and in test messages, for example
;; `(show (Given 5))` is "Given 5". The board formatters in `solver.cl` do not use it
;; (plan-exemplar.md, "HTML is built with `str-concat`").
(impl text.display/Display Cell
  (defn show [self]
    (match self
      [(Given v)      (str-concat "Given " (show v))
       (Solved v)     (str-concat "Solved " (show v))
       (Candidates m) (str-concat "Candidates " (show m))])))

;; ── Tests ───────────────────────────────────────────────────────────────
;;
;; Each `test-*` returns `(Option String)`, `None` for a pass
;; (repl/spec/16-test-discovery.md §16.1). `tests.cl` calls them, and
;; `cranelisp --test` discovers them.

;; --- Bitmask tests ---

(defn test-full-mask []
  (assert-eq 511 (full-mask)))

(defn test-pow2 []
  (check
    (assert-eq 1 (pow2 0))
    (assert-eq 2 (pow2 1))
    (assert-eq 8 (pow2 3))
    (assert-eq 256 (pow2 8))))

(defn test-bit-set? []
  (check
    (assert-true (bit-set? (full-mask) 1))
    (assert-true (bit-set? (full-mask) 5))
    (assert-true (bit-set? (full-mask) 9))
    (assert-false (bit-set? 0 1))))

(defn test-bit-clear []
  (let [cleared (bit-clear (full-mask) 5)]
    (check
      (assert-false (bit-set? cleared 5))
      (assert-true (bit-set? cleared 4))
      (assert-eq 495 cleared))))

(defn test-bit-count []
  (check
    (assert-eq 9 (bit-count (full-mask)))
    (assert-eq 0 (bit-count 0))
    (assert-eq 1 (bit-count 4))))

(defn test-bit-lowest []
  (check
    (assert-eq 1 (bit-lowest (full-mask)))
    (assert-eq 0 (bit-lowest 0))
    (assert-eq 5 (bit-lowest 16))))

;; --- Index helpers ---

(defn test-row-of []
  (check
    (assert-eq 0 (row-of 0))
    (assert-eq 0 (row-of 8))
    (assert-eq 1 (row-of 9))
    (assert-eq 8 (row-of 80))))

(defn test-col-of []
  (check
    (assert-eq 0 (col-of 0))
    (assert-eq 8 (col-of 8))
    (assert-eq 0 (col-of 9))
    (assert-eq 8 (col-of 80))))

(defn test-box-of []
  (check
    (assert-eq 0 (box-of 0))
    (assert-eq 0 (box-of 2))
    (assert-eq 1 (box-of 3))
    (assert-eq 3 (box-of 27))
    (assert-eq 8 (box-of 80))))

;; --- Peers ---

(defn test-peers-count []
  (check
    (assert-eq 20 (count (peers 0)))
    (assert-eq 20 (count (peers 40)))))

;; --- Grid construction ---

(defn test-make-grid-wrong-length []
  (match (make-grid "12345")
    [None None
     _ (Some "make-grid should reject short strings")]))

(defn parsed-cell-name [ch]
  (match (parse-cell ch)
    [None "invalid"
     (Some c) (show c)]))

(defn test-parse-cell []
  (check
    (assert-eq "Given 5" (parsed-cell-name "5"))
    (assert-eq "Candidates 511" (parsed-cell-name "."))
    (assert-eq "Candidates 511" (parsed-cell-name "0"))
    (assert-eq "invalid" (parsed-cell-name "x"))
    (assert-eq "invalid" (parsed-cell-name "12"))))

;; Every row of the hand-built grid holds the givens 1–9 in column order.
(defn build-given-grid []
  (Grid (vec-map (fn [i] (Given (+ (col-of i) 1))) (range 0 81))))

(defn test-cell-at []
  (let [g (build-given-grid)]
    (check
      (assert-eq 1 (cell-value (cell-at g 0)))
      (assert-eq 9 (cell-value (cell-at g 80)))
      (assert-true (cell-determined? (cell-at g 40))))))

(defn test-is-solved-all-given []
  (assert-true (is-solved (build-given-grid))))

(defn test-is-solved-with-candidates []
  (assert-false (is-solved (set-cell (build-given-grid) 0 (Candidates (full-mask))))))

(defn test-set-cell []
  (let [g (set-cell (build-given-grid) 5 (Solved 7))]
    (match (cell-at g 5)
      [(Solved v) (assert-eq 7 v)
       _ (Some "cell 5 should be Solved")])))
