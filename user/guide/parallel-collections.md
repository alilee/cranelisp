# Parallel collections — `par-map`, `par-reduce`, `par-map-reduce`

The standard library's `collections.parallel` module gives you three combinators
that run their per-element work across CPU cores automatically:

| Function | What it does | Sequential twin |
|---|---|---|
| `par-map` | Apply `f` to every element of a Vec, returning a new Vec. | `vec-map` |
| `par-reduce` | Combine a Vec's elements with an **associative** `f` and an identity `init`. | `vec-reduce` |
| `par-map-reduce` | Map `mapf` over each element, then combine with an **associative** `redf`. | `vec-reduce ∘ vec-map` |

They are **ordinary library functions** — there is no new syntax, no `spark`, no
`par`, no threads in your code. You call them exactly like `map` and `reduce`; the
parallelism comes from the compiler's automatic lenient-evaluation substrate (see
[automatic parallelism](../getting-started.md#automatic-parallelism)). Open
`stdlib/collections/parallel.cl` and you will find plain divide-and-conquer recursion
— nothing magic.

## Importing them

They are **import-on-demand**, not part of the prelude. Pull in the ones you need:

```clojure
(import [collections.parallel [par-map par-reduce par-map-reduce]])
```

## Using them

```clojure
;; Apply an expensive function to every element, in parallel.
(par-map expensive-fn v)

;; Sum a Vec in parallel. `add` is associative; 0 is its identity.
(par-reduce add 0 v)

;; Map then reduce, fused (no intermediate Vec).
(par-map-reduce expensive-fn add 0 v)
```

## The contract: same answers as the sequential version

**Correctness is the contract; parallelism is a performance property.** Each function
returns a result **identical** to its sequential twin:

- `par-map` == `vec-map` — element-for-element, order preserved.
- `par-reduce` == `vec-reduce` — **provided `f` is associative and `init` is its
  identity**. Unlike `vec-reduce`, here `f` combines two *partial results* of the same
  type — `(Fn [a a] a)` — so a non-associative `f` (e.g. subtraction) is a misuse, not
  supported.
- `par-map-reduce` == `vec-reduce ∘ vec-map`, with the same associativity requirement
  on `redf`.

Because the language is pure, evaluation order never changes results. You can force a
fully serial run for a baseline or for debugging and get the same answer either way:
`CRANELISP_NO_LENIENT=1` or `CRANELISP_SPARK_BUDGET=0` (see the
[environment variables](../cli-reference.md#environment-variables)).

## When it pays off — and when it does not

Parallelism here is a **performance property with a known limit**, not a blanket
speedup. Use these functions when each chunk of work is **compute-bound and
substantial** — roughly a microsecond or more of arithmetic-style work per element.
On that kind of workload the parallel run is genuinely faster (around 2–3× has been
observed on the compute-bound map-reduce example) and never meaningfully slower than
serial.

**The honest caveat:** for **allocation-heavy or reference-counting-heavy** workloads
— code where each element copies or builds large heap structures rather than crunching
numbers — `par-*` can currently be **slower** than the plain sequential `vec-map` /
`vec-reduce`. The parallel branches are genuinely independent, but they contend on two
shared, serializing resources: the global memory allocator and atomic reference-count
updates bouncing between worker cores. The "never slower than serial" floor holds
**unconditionally only for compute-bound work**; for allocation-/RC-heavy work it is
contention-bounded and can be violated (measured up to ~10× on a copy-per-element
workload). The path back to a guaranteed floor (a contention-aware decision to keep
such branches sequential) is tracked in
[`design/arch/effect-concurrency.md §3.1`](../../design/arch/effect-concurrency.md).

**Rule of thumb:** reach for `par-*` on compute-bound chunked work; measure before
relying on it for allocation-heavy work, and keep the sequential `vec-map` / `vec-reduce`
as your baseline (`CRANELISP_NO_LENIENT=1`) to compare against.

## Tuning and disabling

The same knobs that govern all automatic parallelism apply here:

- `CRANELISP_SPARK_BUDGET=N` — cap how much pure work runs in parallel at once; `0`
  disables auto-parallelism entirely.
- `CRANELISP_NO_LENIENT=1` — force strictly serial evaluation (your sequential
  baseline).

Both are documented in
[`cli-reference.md` § environment variables](../cli-reference.md#environment-variables).

## See also

- [Automatic parallelism](../getting-started.md#automatic-parallelism) — the model
  these functions build on.
- [`examples/30-parallel-map-reduce.cl`](../../examples/30-parallel-map-reduce.cl) —
  the worked divide-and-conquer map-reduce.
- [`spec/12-runtime.md §12.4.3`](../../spec/12-runtime.md) — lenient evaluation
  (normative).
- [`design/arch/effect-concurrency.md §3.1`](../../design/arch/effect-concurrency.md) —
  the performance floor, its scope, and the known contention limit.
