;; num/bits.cl — Bitwise operations on non-negative integers
;;
;; Cranelisp has no bitwise primitives (band/bor/bxor/bnot/ishl/ushr/popcnt).
;; FIXME 0416 proposes adding them as COMPILER intrinsics; that decision is
;; DEFERRED (a future perf-driven call by /arch + /backend). This module
;; provides the same surface NOW, composed entirely from existing Ring 0
;; arithmetic primitives (`+ - * / rem`), so the bitmask/flags/sets-as-masks
;; domain has a clean, reusable `num.bits` API today.
;;
;; ── WIDTH ──────────────────────────────────────────────────────────────
;; The fixed-width ops — `bit-and`, `bit-or`, `bit-xor`, `bit-not`, and
;; `popcount` — operate over a documented WIDTH of **30 bits** (bit positions
;; 0..29). 30 keeps every intermediate (incl. `(pow2 WIDTH)` and a fully-set
;; mask) comfortably inside the positive Int range, so the arithmetic
;; simulation never touches the sign bit — `bit-not x` is the *one's
;; complement within the low 30 bits*, NOT a machine two's-complement. This
;; is the right model for bitmask domains (flags, candidate sets, small bit
;; fields); operands are expected non-negative and < 2^30.
;;
;; ── COMPOSITION ────────────────────────────────────────────────────────
;;   (1 << n)      ≡  (pow2 n)                     ; repeated *2
;;   (x << n)      ≡  (* x (pow2 n))               ; bit-shift-left
;;   (x >> n)      ≡  (/ x (pow2 n))               ; bit-shift-right (logical)
;;   bit n of x    ≡  (rem (/ x (pow2 n)) 2)       ; 0 or 1
;;   and/or/xor    ≡  bit-by-bit fold over 0..WIDTH, re-weighting each result
;;                    bit by its place value (pow2 i)
;;   bit-not x     ≡  (- (full-mask) x)            ; one's complement in WIDTH
;;   popcount x    ≡  count of set bits over 0..WIDTH
;;
;; These match the Clojure standard-library names (`bit-and`, `bit-or`,
;; `bit-xor`, `bit-not`, `bit-shift-left`, `bit-shift-right`, `bit-test`,
;; `bit-set`, `bit-clear`, `bit-flip`). None are reserved by
;; spec/11-stdlib.md §11.4a, so they are safe to define here (reached
;; module-qualified / via import — NOT bare-promoted to the prelude).
;;
;; Spec: plan-stdlib.md §3.3, §26.4 (gap G1 / FIXME 0416 stdlib coverage)

(import [prelude []])
(import [primitives [*]])

;; The fixed bit width for the closed-over (and/or/xor/not/popcount) ops.
(defn width "Bit width of the fixed-width ops (30)" [] :Int 30)

;; 2^n by repeated multiplication. Defined for n >= 0.
(defn pow2 "Compute 2^n for n >= 0" [:Int n] :Int
  (if (eq-i64 n 0) 1
    (mul-i64 2 (pow2 (sub-i64 n 1)))))

;; All low-WIDTH bits set: 2^WIDTH - 1. Used as the bit-not complement base.
(defn full-mask "Mask with all low `width` bits set (2^width - 1)" [] :Int
  (sub-i64 (pow2 (width)) 1))

;; ── Shifts ───────────────────────────────────────────────────────────────

(defn bit-shift-left "Logical left shift: x << n  (x * 2^n)"
  [:Int x :Int n] :Int
  (mul-i64 x (pow2 n)))

(defn bit-shift-right "Logical right shift: x >> n  (x / 2^n), x >= 0"
  [:Int x :Int n] :Int
  (div-i64 x (pow2 n)))

;; ── Single-bit operations ─────────────────────────────────────────────────

;; Value (0 or 1) of bit at position n.
(defn bit-at "The value (0 or 1) of bit n of x" [:Int x :Int n] :Int
  (sub-i64 (div-i64 x (pow2 n)) (mul-i64 2 (div-i64 x (pow2 (add-i64 n 1))))))

(defn bit-test "True iff bit n of x is set" [:Int x :Int n] :Bool
  (eq-i64 (bit-at x n) 1))

(defn bit-set "Set bit n of x to 1" [:Int x :Int n] :Int
  (if (bit-test x n) x (add-i64 x (pow2 n))))

(defn bit-clear "Clear bit n of x to 0" [:Int x :Int n] :Int
  (if (bit-test x n) (sub-i64 x (pow2 n)) x))

(defn bit-flip "Toggle bit n of x" [:Int x :Int n] :Int
  (if (bit-test x n) (sub-i64 x (pow2 n)) (add-i64 x (pow2 n))))

;; ── Fixed-width logical ops (fold over bit positions 0..width) ────────────

;; Per-bit combine of a and b under op `f` (each f arg is 0/1, result 0/1),
;; re-weighting bit i by its place value (pow2 i), accumulating from bit i up.
(defn- bit-fold2 [f :Int a :Int b :Int i :Int acc] :Int
  (if (ge-i64 i (width)) acc
    (bit-fold2 f a b (add-i64 i 1)
      (add-i64 acc (mul-i64 (f (bit-at a i) (bit-at b i)) (pow2 i))))))

(defn- and-bit [:Int p :Int q] :Int (if (eq-i64 (add-i64 p q) 2) 1 0))
(defn- or-bit  [:Int p :Int q] :Int (if (eq-i64 (add-i64 p q) 0) 0 1))
(defn- xor-bit [:Int p :Int q] :Int (if (eq-i64 (add-i64 p q) 1) 1 0))

(defn bit-and "Bitwise AND of a and b (low `width` bits)" [:Int a :Int b] :Int
  (bit-fold2 and-bit a b 0 0))

(defn bit-or "Bitwise OR of a and b (low `width` bits)" [:Int a :Int b] :Int
  (bit-fold2 or-bit a b 0 0))

(defn bit-xor "Bitwise XOR of a and b (low `width` bits)" [:Int a :Int b] :Int
  (bit-fold2 xor-bit a b 0 0))

;; One's complement within the low `width` bits (NOT machine two's-complement).
(defn bit-not "Bitwise NOT of x within the low `width` bits" [:Int x] :Int
  (sub-i64 (full-mask) x))

;; ── Popcount ──────────────────────────────────────────────────────────────

(defn- popcount-from [:Int x :Int i :Int acc] :Int
  (if (ge-i64 i (width)) acc
    (popcount-from x (add-i64 i 1) (add-i64 acc (bit-at x i)))))

(defn popcount "Number of set bits in the low `width` bits of x" [:Int x] :Int
  (popcount-from x 0 0))

;; ── Self-tests ───────────────────────────────────────────────────────
;; `(mod test …)` submodule (S87 hygiene): exercises every op against known
;; values via the in-language harness. Body in bits/test.cl (extraction-stable
;; backing file, spec §8.2.5).

(mod test)
