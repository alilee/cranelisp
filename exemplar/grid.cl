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

(import [collections.vec [count get assoc conj]])
(import [primitives [char-at str-len str-concat not]])
;; `num.bits/bit-clear` and `bit-set` are not imported: grid defines
;; digit-domain verbs of the same names.
(import [num.bits [bit-shift-left bit-test bit-and bit-or bit-not popcount]])

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

;; Parse an 81-character string into a Grid.
;; Digits '1'-'9' become Given cells.
;; Dots '.' become Candidates with full-mask (all digits possible).
;; Returns None if the string is not exactly 81 characters,
;; or contains invalid characters.
;;
;; NOTE: This function depends on `char-at` (a string primitive).
;; `char-at` returns a 1-char String, compared with `=` (Eq on String).
(defn make-grid
  ([s]
   (if (= (str-len s) 81)
     (make-grid s 0 [])
     None))
  ([s i cells]
   (if (= i 81) (Some (Grid cells))
     (let [ch (char-at s i)]
       (if (= ch ".")
         (make-grid s (+ i 1) (conj cells (Candidates (full-mask))))
         ;; Try to parse as a digit 1-9.
         ;; We compare the character against digit strings.
         (if (= ch "1") (make-grid s (+ i 1) (conj cells (Given 1)))
         (if (= ch "2") (make-grid s (+ i 1) (conj cells (Given 2)))
         (if (= ch "3") (make-grid s (+ i 1) (conj cells (Given 3)))
         (if (= ch "4") (make-grid s (+ i 1) (conj cells (Given 4)))
         (if (= ch "5") (make-grid s (+ i 1) (conj cells (Given 5)))
         (if (= ch "6") (make-grid s (+ i 1) (conj cells (Given 6)))
         (if (= ch "7") (make-grid s (+ i 1) (conj cells (Given 7)))
         (if (= ch "8") (make-grid s (+ i 1) (conj cells (Given 8)))
         (if (= ch "9") (make-grid s (+ i 1) (conj cells (Given 9)))
         ;; '0' treated as empty (like '.')
         (if (= ch "0") (make-grid s (+ i 1) (conj cells (Candidates (full-mask))))
           None)))))))))))))))

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
;; Renders a Cell at the REPL and in debug output, for example `(show (Given 5))`
;; is "Given 5". The board formatters in `solver.cl` do not use it
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
  (if (= (full-mask) 511) None (Some "full-mask should equal 511")))

(defn test-pow2 []
  (if (= (pow2 0) 1)
    (if (= (pow2 1) 2)
      (if (= (pow2 3) 8)
        (if (= (pow2 8) 256) None
          (Some "pow2 8 should equal 256"))
        (Some "pow2 3 should equal 8"))
      (Some "pow2 1 should equal 2"))
    (Some "pow2 0 should equal 1")))

(defn test-bit-set? []
  ;; full-mask has all bits set; 0 has no bits set
  (if (bit-set? (full-mask) 1)
    (if (bit-set? (full-mask) 5)
      (if (bit-set? (full-mask) 9)
        (if (not (bit-set? 0 1)) None
          (Some "bit 1 should not be set in 0"))
        (Some "bit 9 should be set in full-mask"))
      (Some "bit 5 should be set in full-mask"))
    (Some "bit 1 should be set in full-mask")))

(defn test-bit-clear []
  ;; Clear digit 5 from full mask: 511 - 16 = 495
  (let [cleared (bit-clear (full-mask) 5)]
    (if (not (bit-set? cleared 5))
      (if (bit-set? cleared 4) None
        (Some "bit 4 should still be set after clearing 5"))
      (Some "bit 5 should be cleared"))))

(defn test-bit-count []
  (if (= (bit-count (full-mask)) 9)
    (if (= (bit-count 0) 0)
      ;; single bit: digit 3 = bit 2 = value 4
      (if (= (bit-count 4) 1) None
        (Some "bit-count of 4 should be 1"))
      (Some "bit-count of 0 should be 0"))
    (Some "bit-count of full-mask should be 9")))

(defn test-bit-lowest []
  (if (= (bit-lowest (full-mask)) 1)
    (if (= (bit-lowest 0) 0)
      ;; mask with only digit 5 set: 2^4 = 16
      (if (= (bit-lowest 16) 5) None
        (Some "bit-lowest of 16 should be 5"))
      (Some "bit-lowest of 0 should be 0"))
    (Some "bit-lowest of full-mask should be 1")))

;; --- Index helpers ---

(defn test-row-of []
  (if (= (row-of 0) 0)
    (if (= (row-of 8) 0)
      (if (= (row-of 9) 1)
        (if (= (row-of 80) 8) None
          (Some "row-of 80 should be 8"))
        (Some "row-of 9 should be 1"))
      (Some "row-of 8 should be 0"))
    (Some "row-of 0 should be 0")))

(defn test-col-of []
  (if (= (col-of 0) 0)
    (if (= (col-of 8) 8)
      (if (= (col-of 9) 0)
        (if (= (col-of 80) 8) None
          (Some "col-of 80 should be 8"))
        (Some "col-of 9 should be 0"))
      (Some "col-of 8 should be 8"))
    (Some "col-of 0 should be 0")))

(defn test-box-of []
  (if (= (box-of 0) 0)
    (if (= (box-of 2) 0)
      (if (= (box-of 3) 1)
        (if (= (box-of 27) 3)
          (if (= (box-of 80) 8) None
            (Some "box-of 80 should be 8"))
          (Some "box-of 27 should be 3"))
        (Some "box-of 3 should be 1"))
      (Some "box-of 2 should be 0"))
    (Some "box-of 0 should be 0")))

;; --- Peers ---

(defn test-peers-count []
  ;; Every cell has exactly 20 peers
  (if (= (count (peers 0)) 20)
    (if (= (count (peers 40)) 20) None
      (Some "cell 40 should have 20 peers"))
    (Some "cell 0 should have 20 peers")))

;; --- Grid construction ---

(defn test-make-grid-wrong-length []
  ;; Too short — should return None
  (match (make-grid "12345")
    [None None
     _ (Some "make-grid should reject short strings")]))

;; Helper for hand-building grids (no `let`-recursion shenanigans).
(defn build-given-grid-helper [v i]
  (if (= i 81) v
    (build-given-grid-helper
      (conj v (Given (+ (rem-i64 i 9) 1)))
      (+ i 1))))

(defn build-given-grid []
  (Grid (build-given-grid-helper [] 0)))

;; Verify cell-at, set-cell, is-solved with a hand-built grid
(defn test-cell-at-and-set []
  (let [g (build-given-grid)
        c0 (cell-at g 0)]
    (match c0
      [(Given v) (if (= v 1) None
                   (Some "cell 0 should be Given 1"))
       _ (Some "cell 0 should be Given")])))

(defn test-is-solved-all-given []
  ;; A grid of all Given cells is solved
  (if (is-solved (build-given-grid)) None
    (Some "all-Given grid should be solved")))

(defn build-grid-with-candidates-helper [v i]
  (if (= i 81) v
    (if (= i 0)
      (build-grid-with-candidates-helper (conj v (Candidates (full-mask))) (+ i 1))
      (build-grid-with-candidates-helper (conj v (Given (+ (rem-i64 i 9) 1))) (+ i 1)))))

(defn test-is-solved-with-candidates []
  ;; A grid with a Candidates cell is not solved
  (let [g (Grid (build-grid-with-candidates-helper [] 0))]
    (if (is-solved g)
      (Some "grid with Candidates cell should not be solved")
      None)))

(defn build-all-given-1-helper [v i]
  (if (= i 81) v
    (build-all-given-1-helper (conj v (Given 1)) (+ i 1))))

(defn test-set-cell []
  ;; set-cell should replace the cell at the given index
  (let [g (Grid (build-all-given-1-helper [] 0))
        g2 (set-cell g 5 (Solved 7))
        c (cell-at g2 5)]
    (match c
      [(Solved v) (if (= v 7) None
                    (Some "cell 5 should be Solved 7"))
       _ (Some "cell 5 should be Solved")])))
