;; num/bits/test.cl — self-tests for num.bits (module num.bits.test)
;;
;; Separate backing file (extraction-stable per spec §8.2.5). Parent declares
;; `(mod test)`. Exercises every bitwise op against known values via the
;; in-language harness.
;;
;; Reference values (decimal ↔ binary):
;;   12 = 0b1100   10 = 0b1010
;;   12 & 10 =  8 = 0b1000
;;   12 | 10 = 14 = 0b1110
;;   12 ^ 10 =  6 = 0b0110

(import [super [pow2 width full-mask
                bit-shift-left bit-shift-right
                bit-at bit-test bit-set bit-clear bit-flip
                bit-and bit-or bit-xor bit-not popcount]])
(import [testing.assertions [assert-true assert-false assert-eq]])
(import [primitives [Option String]])

(defn test-pow2 [] :(Option String)
  (assert-eq 256 (pow2 8)))

(defn test-pow2-zero [] :(Option String)
  (assert-eq 1 (pow2 0)))

(defn test-full-mask [] :(Option String)
  ;; 2^30 - 1
  (assert-eq 1073741823 (full-mask)))

(defn test-shift-left [] :(Option String)
  (assert-eq 40 (bit-shift-left 5 3)))

(defn test-shift-right [] :(Option String)
  (assert-eq 5 (bit-shift-right 40 3)))

(defn test-bit-at-set [] :(Option String)
  ;; bit 2 of 0b1100 is 1
  (assert-eq 1 (bit-at 12 2)))

(defn test-bit-at-clear [] :(Option String)
  ;; bit 0 of 0b1100 is 0
  (assert-eq 0 (bit-at 12 0)))

(defn test-bit-test-true [] :(Option String)
  (assert-true (bit-test 12 3)))

(defn test-bit-test-false [] :(Option String)
  (assert-false (bit-test 12 1)))

(defn test-bit-set [] :(Option String)
  ;; set bit 0 of 0b1100 -> 0b1101 = 13
  (assert-eq 13 (bit-set 12 0)))

(defn test-bit-set-idempotent [] :(Option String)
  ;; setting an already-set bit is a no-op
  (assert-eq 12 (bit-set 12 2)))

(defn test-bit-clear [] :(Option String)
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

(defn test-bit-and [] :(Option String)
  (assert-eq 8 (bit-and 12 10)))

(defn test-bit-or [] :(Option String)
  (assert-eq 14 (bit-or 12 10)))

(defn test-bit-xor [] :(Option String)
  (assert-eq 6 (bit-xor 12 10)))

(defn test-bit-not [] :(Option String)
  ;; ~0 in low 30 bits = full-mask; ~full-mask = 0
  (assert-eq 0 (bit-not (full-mask))))

(defn test-bit-not-roundtrip [] :(Option String)
  ;; not(not(x)) = x  for x within width
  (assert-eq 12 (bit-not (bit-not 12))))

(defn test-popcount [] :(Option String)
  ;; 0b1100 has 2 set bits
  (assert-eq 2 (popcount 12)))

(defn test-popcount-zero [] :(Option String)
  (assert-eq 0 (popcount 0)))

(defn test-popcount-full [] :(Option String)
  ;; full-mask has `width` set bits
  (assert-eq 30 (popcount (full-mask))))
