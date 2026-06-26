;; 31-bitwise.cl -- Bitwise integer operations and bitmask sets
;;
;; `Int` is a signed 64-bit value (example 01). This example treats that
;; same Int as a *bag of 64 bits* and uses the bitwise primitives to read,
;; set, clear, and count individual bits. The motivating picture is a
;; permission bitmask: one Int carries a whole set of yes/no flags, one bit
;; per flag, and the bitwise operators are the set operations on it.
;;
;; The seven bitwise primitives (spec appendix-a-builtins.md §A.3). They are
;; language primitives, not stdlib -- imported directly from `primitives`,
;; exactly like the arithmetic primitives, and lower 1:1 to a CLIF op:
;;
;;   (bit-and a b)   ;; AND  -- a bit is set iff set in BOTH operands
;;   (bit-or  a b)   ;; OR   -- a bit is set iff set in EITHER operand
;;   (bit-xor a b)   ;; XOR  -- a bit is set iff set in EXACTLY ONE operand
;;   (bit-not a)     ;; NOT  -- complement all 64 bits (two's complement)
;;   (shl a n)       ;; left shift  -- vacated low bits are zero-filled
;;   (shr a n)       ;; right shift -- ARITHMETIC on signed Int (sign-extends)
;;   (popcount a)    ;; population count -- how many of the 64 bits are set
;;
;; Two semantics worth pinning down up front:
;;   * `bit-not` works over the FULL 64-bit width, so (bit-not 0) is -1
;;     (all bits set), not 1. Algebraically (bit-not x) = (- (- x) 1).
;;   * `shr` is arithmetic for the current signed Int: the sign bit is
;;     replicated into the vacated high bits, so a negative number stays
;;     negative. (shr -8 1) is -4, not a huge positive value.

(import [primitives [bit-and bit-or bit-xor bit-not shl shr popcount]])

;; 1 if the boolean holds, 0 otherwise -- lets each sub-test contribute a
;; pass count to `main` (example 02's pattern).
(defn b2i [b] (if b 1 0))

;; --- Single-bit helpers, defined inline from the primitives ---------------
;;
;; A "bit position" n names the bit worth 2^n. The mask for that single bit
;; is (shl 1 n): a 1 shifted left into position n. Everything below is built
;; from that one idea plus the four logical primitives.

;; Is bit n set in x? Shift the bit down to position 0 and AND off the rest.
(defn bit-test [x n] (eq-i64 (bit-and (shr x n) 1) 1))

;; Return x with bit n turned on: OR in the single-bit mask.
(defn bit-set [x n] (bit-or x (shl 1 n)))

;; Return x with bit n turned off: AND with the COMPLEMENT of the mask, so
;; every bit survives except position n. This is where bit-not earns its
;; full-width semantics -- the complement has all other 63 bits set.
(defn bit-clear [x n] (bit-and x (bit-not (shl 1 n))))

;; Return x with bit n toggled: XOR flips exactly the masked bit.
(defn bit-flip [x n] (bit-xor x (shl 1 n)))

;; How many bits are set across the whole 64-bit value -- i.e. the size of
;; the set this bitmask represents.
(defn count-bits [x] (popcount x))

;; --- A permission bitmask -------------------------------------------------
;;
;; Name three flags by their bit positions. The mask for a flag is (shl 1 p).
;; A "permission set" is a single Int whose set bits are the granted flags.
(defn flag-read  [] 0)   ;; bit 0  -> mask 0b001 = 1
(defn flag-write [] 1)   ;; bit 1  -> mask 0b010 = 2
(defn flag-exec  [] 2)   ;; bit 2  -> mask 0b100 = 4

;; Build read+write+exec by setting each flag's bit in turn, starting from
;; the empty set (0). Result is 0b111 = 7.
(defn all-perms []
  (bit-set (bit-set (bit-set 0 (flag-read)) (flag-write)) (flag-exec)))

;; "Can write?" is membership of the write bit in the permission set.
(defn can-write? [perms] (bit-test perms (flag-write)))

;; Union of two permission sets is OR; intersection is AND. These ARE the
;; set operations -- no separate set type is needed.
(defn perms-union        [a b] (bit-or  a b))
(defn perms-intersection [a b] (bit-and a b))

;; --- Sub-tests ------------------------------------------------------------
;;
;; Each returns 1 on success, so `main`'s total is the number of passing
;; checks; a drop below the expected total flags a regression.

;; Logical primitives on two 4-bit patterns: 0b1100 (12) and 0b1010 (10).
;;   AND -> 0b1000 = 8 ; OR -> 0b1110 = 14 ; XOR -> 0b0110 = 6
(defn test-and [] (b2i (eq-i64 (bit-and 12 10) 8)))
(defn test-or  [] (b2i (eq-i64 (bit-or  12 10) 14)))
(defn test-xor [] (b2i (eq-i64 (bit-xor 12 10) 6)))

;; Full-width complement: (bit-not 0) sets all 64 bits = -1.
(defn test-not [] (b2i (eq-i64 (bit-not 0) -1)))

;; Left shift zero-fills: 1 << 4 = 16.
(defn test-shl [] (b2i (eq-i64 (shl 1 4) 16)))

;; Arithmetic right shift keeps the sign: -8 >> 1 = -4.
(defn test-shr-arith [] (b2i (eq-i64 (shr -8 1) -4)))

;; Shift count is taken modulo 64, so shifting by 64 is the same as by 0.
(defn test-shift-mod-64 [] (b2i (eq-i64 (shl 1 64) 1)))

;; popcount counts set bits regardless of where they sit: 0b11111111 = 255
;; has 8 set bits.
(defn test-popcount [] (b2i (eq-i64 (popcount 255) 8)))

;; Single-bit membership: bit 0 of 0b101 is set; bit 1 is not.
(defn test-bit-test [] (b2i (bit-test 5 0)))
(defn test-bit-test-neg [] (b2i (not (bit-test 5 1))))

;; set / clear / flip a single bit.
(defn test-bit-set   [] (b2i (eq-i64 (bit-set 0 3) 8)))     ;; 0 -> 0b1000
(defn test-bit-clear [] (b2i (eq-i64 (bit-clear 15 0) 14))) ;; 0b1111 -> 0b1110
(defn test-bit-flip  [] (b2i (eq-i64 (bit-flip 0 5) 32)))   ;; 0 -> 0b100000

;; The permission bitmask in action.
(defn test-all-perms []
  (b2i (eq-i64 (all-perms) 7)))                 ;; read+write+exec = 0b111
(defn test-can-write []
  (b2i (can-write? (all-perms))))               ;; write bit is set
(defn test-revoke-write []
  ;; Clear the write bit, then confirm it is gone but the others remain.
  (let [reduced (bit-clear (all-perms) (flag-write))]
    (b2i (if (can-write? reduced) false true))))
(defn test-count-perms []
  ;; popcount of the full mask is the number of granted permissions: 3.
  (b2i (eq-i64 (count-bits (all-perms)) 3)))

;; Union and intersection of two permission sets, as set operations.
(defn test-perms-union []
  ;; {read} ∪ {write} = {read,write} = 0b011 = 3
  (let [r (bit-set 0 (flag-read))
        w (bit-set 0 (flag-write))]
    (b2i (eq-i64 (perms-union r w) 3))))
(defn test-perms-intersection []
  ;; {read,write} ∩ {write,exec} = {write} = 0b010 = 2
  (let [rw (bit-or (bit-set 0 (flag-read))  (bit-set 0 (flag-write)))
        we (bit-or (bit-set 0 (flag-write)) (bit-set 0 (flag-exec)))]
    (b2i (eq-i64 (perms-intersection rw we) 2))))

;; Expected total: 19 passing sub-tests.
(defn main []
  ;; Wrap the sum-of-pass-counts in `Pure`: every batch `main` must
  ;; return `IO _`. The inner Int is the exit code (preserved).
  (Pure
    (add-i64 (test-and)
      (add-i64 (test-or)
        (add-i64 (test-xor)
          (add-i64 (test-not)
            (add-i64 (test-shl)
              (add-i64 (test-shr-arith)
                (add-i64 (test-shift-mod-64)
                  (add-i64 (test-popcount)
                    (add-i64 (test-bit-test)
                      (add-i64 (test-bit-test-neg)
                        (add-i64 (test-bit-set)
                          (add-i64 (test-bit-clear)
                            (add-i64 (test-bit-flip)
                              (add-i64 (test-all-perms)
                                (add-i64 (test-can-write)
                                  (add-i64 (test-revoke-write)
                                    (add-i64 (test-count-perms)
                                      (add-i64 (test-perms-union)
                                        (test-perms-intersection)))))))))))))))))))))
