;; num/bits.cl — Bitwise operations on 64-bit integers
;;
;; A curated, Clojure-aligned convenience layer over the S91 native bitwise
;; primitives (`bit-and`, `bit-or`, `bit-xor`, `bit-not`, `shl`, `shr`,
;; `popcount`; spec appendix-a-builtins §A.3, FIXME 0416). The primitives do
;; all the work — each lowers 1:1 to a CLIF op (`band`/`bor`/`bxor`/`bnot`/
;; `ishl`/`sshr`/`popcnt`) with no call overhead. This module is the thin
;; convenience shell on top.
;;
;; ── WIDTH ──────────────────────────────────────────────────────────────
;; Operations act on `Int` as a **full 64-bit two's-complement** value
;; (the language `Int` is signed 64-bit, §A.1). This is a deliberate change
;; from the pre-S91 arithmetic-simulation module, which clamped to a 30-bit
;; one's-complement WIDTH to keep intermediates positive. With native ops
;; there is no width limit: `bit-not` complements all 64 bits, `popcount`
;; counts across all 64, and the sign bit participates like any other.
;;   (bit-not x)  =  (- (- x) 1)         ; full two's-complement: ~0 = -1
;;
;; ── SHIFTS ─────────────────────────────────────────────────────────────
;;   bit-shift-left  = shl  (zero-fills vacated low bits)
;;   bit-shift-right = shr  (ARITHMETIC: sign bit replicated into high bits)
;; Clojure also has `unsigned-bit-shift-right`; S91 ships only the arithmetic
;; `shr` (a logical/unsigned variant is a future per-integer-type concern,
;; §A.3 note), so this module intentionally provides no unsigned variant.
;; The shift count is taken modulo 64 (§A.3).
;;
;; ── BIT-AT-POSITION HELPERS ────────────────────────────────────────────
;; `bit-test`/`bit-set`/`bit-clear`/`bit-flip` are composed from the
;; primitives via the single-bit mask `(shl 1 n)`:
;;   bit-test  mask n  =  (not (= 0 (bit-and mask (shl 1 n))))
;;   bit-set   mask n  =  (bit-or  mask        (shl 1 n))
;;   bit-clear mask n  =  (bit-and mask (bit-not (shl 1 n)))
;;   bit-flip  mask n  =  (bit-xor mask        (shl 1 n))
;;
;; ── NAMING ─────────────────────────────────────────────────────────────
;; All names follow Clojure's `clojure.core` bit-* surface. The primitive
;; names `bit-and`/`bit-or`/`bit-xor`/`bit-not` already match Clojure, so
;; they are re-presented here as thin pass-throughs (giving each a curated
;; docstring + the module's signature convention). None are reserved by
;; spec/11-stdlib.md §11.4a; all are reached module-qualified / via import —
;; NOT bare-promoted to the prelude.
;;
;; Spec: appendix-a-builtins §A.3, plan-stdlib.md §3.3, §26.8

(import [prelude []])
(import [primitives [*]])

;; ── Direct logical ops (thin pass-throughs over the primitives) ───────────

(defn bit-and "Bitwise AND of a and b (all 64 bits)" [:Int a :Int b] :Int
  (primitives/bit-and a b))

(defn bit-or "Bitwise OR of a and b (all 64 bits)" [:Int a :Int b] :Int
  (primitives/bit-or a b))

(defn bit-xor "Bitwise XOR of a and b (all 64 bits)" [:Int a :Int b] :Int
  (primitives/bit-xor a b))

(defn bit-not "Bitwise complement of x (all 64 bits; ~0 = -1)" [:Int x] :Int
  (primitives/bit-not x))

;; ── Shifts ───────────────────────────────────────────────────────────────

(defn bit-shift-left "Left shift: x << n  (zero-fills vacated low bits)"
  [:Int x :Int n] :Int
  (shl x n))

(defn bit-shift-right "Arithmetic right shift: x >> n  (sign-extending)"
  [:Int x :Int n] :Int
  (shr x n))

;; ── Single-bit operations (composed from the primitives) ──────────────────

(defn bit-test "True iff bit n of mask is set" [:Int mask :Int n] :Bool
  (not (eq-i64 0 (primitives/bit-and mask (shl 1 n)))))

(defn bit-set "Set bit n of mask to 1" [:Int mask :Int n] :Int
  (primitives/bit-or mask (shl 1 n)))

(defn bit-clear "Clear bit n of mask to 0" [:Int mask :Int n] :Int
  (primitives/bit-and mask (primitives/bit-not (shl 1 n))))

(defn bit-flip "Toggle bit n of mask" [:Int mask :Int n] :Int
  (primitives/bit-xor mask (shl 1 n)))

;; ── Population count ──────────────────────────────────────────────────────

(defn popcount "Number of set bits in the 64-bit representation of x" [:Int x] :Int
  (primitives/popcount x))

;; Clojure-style alias for popcount.
(defn bit-count "Number of set bits in x (Clojure alias for popcount)" [:Int x] :Int
  (primitives/popcount x))

;; ── Self-tests ───────────────────────────────────────────────────────
;; `(mod test …)` submodule (S87 hygiene): exercises every wrapper against
;; known values via the in-language harness. Body in bits/test.cl
;; (extraction-stable backing file, spec §8.2.5).

(mod test)
