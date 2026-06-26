;; num/bits/test.cl — self-tests for num.bits (module num.bits.test)
;;
;; Separate backing file (extraction-stable per spec §8.2.5). Parent declares
;; `(mod test)`. Exercises every bitwise wrapper against known values via the
;; in-language harness. Semantics are full 64-bit two's-complement (S91 native
;; primitives) — the sign bit participates and `bit-not` is full-width.
;;
;; Reference values (decimal ↔ binary):
;;   12 = 0b1100   10 = 0b1010
;;   12 & 10 =  8 = 0b1000
;;   12 | 10 = 14 = 0b1110
;;   12 ^ 10 =  6 = 0b0110

(import [super [bit-and bit-or bit-xor bit-not
                bit-shift-left bit-shift-right
                bit-test bit-set bit-clear bit-flip
                popcount bit-count]])
(import [testing.assertions [assert-true assert-false assert-eq]])
(import [primitives [Option String]])

;; ── Direct logical ops ────────────────────────────────────────────────────

(defn test-bit-and [] :(Option String)
  (assert-eq 8 (bit-and 12 10)))

(defn test-bit-or [] :(Option String)
  (assert-eq 14 (bit-or 12 10)))

(defn test-bit-xor [] :(Option String)
  (assert-eq 6 (bit-xor 12 10)))

(defn test-bit-and-neg [] :(Option String)
  ;; -1 is all-ones; (and -1 x) = x (sign bit participates)
  (assert-eq 12 (bit-and -1 12)))

;; ── bit-not (full-width two's-complement) ─────────────────────────────────

(defn test-bit-not-zero [] :(Option String)
  ;; ~0 = -1 across all 64 bits
  (assert-eq -1 (bit-not 0)))

(defn test-bit-not-twos-complement [] :(Option String)
  ;; ~x = (- (- x) 1); ~5 = -6
  (assert-eq -6 (bit-not 5)))

(defn test-bit-not-roundtrip [] :(Option String)
  ;; not(not(x)) = x  for any 64-bit x
  (assert-eq 12 (bit-not (bit-not 12))))

;; ── Shifts ────────────────────────────────────────────────────────────────

(defn test-shift-left [] :(Option String)
  (assert-eq 40 (bit-shift-left 5 3)))

(defn test-shift-right [] :(Option String)
  (assert-eq 5 (bit-shift-right 40 3)))

(defn test-shift-right-arithmetic [] :(Option String)
  ;; arithmetic (sign-extending) right shift: -8 >> 1 = -4
  (assert-eq -4 (bit-shift-right -8 1)))

(defn test-shift-left-sign-bit [] :(Option String)
  ;; shifting 1 into bit 63 yields the most-negative Int
  (assert-eq -9223372036854775808 (bit-shift-left 1 63)))

;; ── Single-bit operations: bit 0 ──────────────────────────────────────────

(defn test-bit-test-low-true [] :(Option String)
  ;; bit 3 of 0b1100 is set
  (assert-true (bit-test 12 3)))

(defn test-bit-test-low-false [] :(Option String)
  ;; bit 0 of 0b1100 is clear
  (assert-false (bit-test 12 0)))

(defn test-bit-set-low [] :(Option String)
  ;; set bit 0 of 0b1100 -> 0b1101 = 13
  (assert-eq 13 (bit-set 12 0)))

(defn test-bit-set-idempotent [] :(Option String)
  ;; setting an already-set bit is a no-op
  (assert-eq 12 (bit-set 12 2)))

(defn test-bit-clear-low [] :(Option String)
  ;; clear bit 2 of 0b1100 -> 0b1000 = 8
  (assert-eq 8 (bit-clear 12 2)))

(defn test-bit-clear-noop [] :(Option String)
  ;; clearing an already-clear bit is a no-op
  (assert-eq 12 (bit-clear 12 0)))

(defn test-bit-flip-on [] :(Option String)
  ;; flip clear bit 0 of 0b1100 -> 0b1101 = 13
  (assert-eq 13 (bit-flip 12 0)))

(defn test-bit-flip-off [] :(Option String)
  ;; flip set bit 2 of 0b1100 -> 0b1000 = 8
  (assert-eq 8 (bit-flip 12 2)))

;; ── Single-bit operations: high bit (bit 62) ──────────────────────────────

(defn test-bit-set-high [] :(Option String)
  ;; set bit 62 of 0 = 2^62 = 4611686018427387904
  (assert-eq 4611686018427387904 (bit-set 0 62)))

(defn test-bit-test-high [] :(Option String)
  ;; after setting bit 62, bit-test sees it
  (assert-true (bit-test (bit-set 0 62) 62)))

(defn test-bit-clear-high [] :(Option String)
  ;; set then clear bit 62 -> 0
  (assert-eq 0 (bit-clear (bit-set 0 62) 62)))

(defn test-bit-test-sign-bit [] :(Option String)
  ;; the most-negative Int has bit 63 set
  (assert-true (bit-test -9223372036854775808 63)))

;; ── Population count ──────────────────────────────────────────────────────

(defn test-popcount [] :(Option String)
  ;; 0b1100 has 2 set bits
  (assert-eq 2 (popcount 12)))

(defn test-popcount-zero [] :(Option String)
  (assert-eq 0 (popcount 0)))

(defn test-popcount-all-ones [] :(Option String)
  ;; -1 is all 64 bits set
  (assert-eq 64 (popcount -1)))

(defn test-bit-count-alias [] :(Option String)
  ;; bit-count is the Clojure alias for popcount
  (assert-eq 2 (bit-count 12)))
