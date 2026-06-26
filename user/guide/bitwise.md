# Bitwise operations

Cranelisp gives you bit-level arithmetic on `Int` — which is a signed **64-bit**
two's-complement value. There are two layers: a set of native **primitives** (one
machine instruction each) and a curated **`num.bits`** standard-library module with
Clojure-style names and a few composed helpers.

## The primitives

The primitives live in the `primitives` module. Import the ones you use:

```clojure
(import [primitives [bit-and bit-or bit-xor bit-not shl shr popcount]])
```

| Primitive | Type | What it does |
|---|---|---|
| `bit-and` | `(Fn [Int Int] Int)` | Bitwise AND |
| `bit-or` | `(Fn [Int Int] Int)` | Bitwise OR |
| `bit-xor` | `(Fn [Int Int] Int)` | Bitwise XOR |
| `bit-not` | `(Fn [Int] Int)` | Bitwise complement (all 64 bits) |
| `shl` | `(Fn [Int Int] Int)` | Left shift — vacated low bits are zero-filled |
| `shr` | `(Fn [Int Int] Int)` | Right shift — **arithmetic** (see the gotcha below) |
| `popcount` | `(Fn [Int] Int)` | Population count — number of set bits |

At the REPL (every result in `:Type value` notation):

```
user> (bit-and 12 10)
:primitives/Int 8
user> (bit-or 12 10)
:primitives/Int 14
user> (bit-xor 12 10)
:primitives/Int 6
user> (bit-not 0)
:primitives/Int -1
user> (shl 1 4)
:primitives/Int 16
user> (popcount 255)
:primitives/Int 8
```

### Width and shifts — the details

- **All 64 bits participate.** `bit-not` complements the full 64-bit
  representation, so `(bit-not 0)` is `-1`. `popcount` counts set bits across all 64.
  Equivalently, `(bit-not x)` is `(- (- x) 1)`.
- **`shl` zero-fills.** Left-shifting always shifts zeros into the low bits,
  regardless of sign.
- **The shift count is taken modulo 64.** Shift amounts are not otherwise
  range-checked.

### Gotcha — `shr` is an *arithmetic* right shift

There is one right-shift primitive, `shr`, and on the signed `Int` it is
**arithmetic**: the sign bit is replicated into the vacated high bits. So a negative
number stays negative:

```
user> (shr -8 1)
:primitives/Int -4
```

If you were expecting a *logical* (zero-filling, "unsigned") right shift, `shr` is
not it — Cranelisp does not ship an unsigned right shift today. (A per-type logical
variant is a future concern, tracked alongside other integer types in
[`spec/appendix-a-builtins.md §A.3`](../../spec/appendix-a-builtins.md).)

## The `num.bits` module

`num.bits` is the convenience layer: Clojure-aligned names over the primitives, plus
single-bit helpers you would otherwise compose by hand. It is reached by import (not
bare-promoted into the prelude):

```clojure
(import [num.bits [bit-shift-left bit-shift-right
                   bit-test bit-set bit-clear bit-flip
                   bit-count]])
```

| Function | Type | What it does |
|---|---|---|
| `bit-shift-left` | `(Fn [Int Int] Int)` | `x << n` (zero-fill) — wraps `shl` |
| `bit-shift-right` | `(Fn [Int Int] Int)` | `x >> n` (arithmetic) — wraps `shr` |
| `bit-test` | `(Fn [Int Int] Bool)` | true iff bit `n` of `mask` is set |
| `bit-set` | `(Fn [Int Int] Int)` | set bit `n` to 1 |
| `bit-clear` | `(Fn [Int Int] Int)` | clear bit `n` to 0 |
| `bit-flip` | `(Fn [Int Int] Int)` | toggle bit `n` |
| `bit-count` | `(Fn [Int] Int)` | set-bit count — Clojure alias for `popcount` |

(`num.bits` also re-presents `bit-and`/`bit-or`/`bit-xor`/`bit-not` as thin
pass-throughs with curated docstrings, so you can import the whole bitwise surface
from one place.)

```
user> (bit-shift-left 3 2)
:primitives/Int 12
user> (bit-test 5 0)
:primitives/Bool true
user> (bit-test 5 1)
:primitives/Bool false
user> (bit-set 0 3)
:primitives/Int 8
user> (bit-clear 15 1)
:primitives/Int 13
user> (bit-flip 0 5)
:primitives/Int 32
user> (bit-count 255)
:primitives/Int 8
```

The single-bit helpers are just compositions of the primitives over the one-bit mask
`(shl 1 n)` — for example `bit-set` is `(bit-or mask (shl 1 n))` — so they cost the
same as writing them inline.

Note `num.bits` deliberately ships **no unsigned right shift**: like the primitive
`shr`, `bit-shift-right` is arithmetic. Clojure's `unsigned-bit-shift-right` has no
counterpart here yet.

## See also

- [`spec/appendix-a-builtins.md §A.3`](../../spec/appendix-a-builtins.md) — the
  normative primitive reference (CLIF lowering, exact width/shift semantics).
- The `num.bits` source: [`stdlib/num/bits.cl`](../../stdlib/num/bits.cl).
