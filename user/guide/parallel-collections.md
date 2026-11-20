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
compiler can evaluate independent recursive branches in parallel (see
[automatic parallelism](../getting-started.md#automatic-parallelism)). Open
`stdlib/collections/parallel.cl` and you will find plain divide-and-conquer recursion
— nothing magic.

## Importing them

They are **import-on-demand**, not part of the prelude. Pull in the ones you need:

<!-- sample: {"kind":"definition"} -->
```clojure
(import [collections.parallel [par-map par-reduce par-map-reduce]])
```

## Using them

<!-- sample: {"kind":"illustrative","reason":"Call shapes use application-supplied expensive-fn, add and v"} -->
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

Use these functions for substantial independent computation, then measure with
your actual inputs. Historical compute-bound map-reduce measurements showed
roughly 2–3× speedup; those measurements do not guarantee current performance
or a minimum amount of work per element.

Allocation-heavy work can be slower than sequential `vec-map` or `vec-reduce`:
workers contend on allocation and reference counting. Keep the sequential twin
and `CRANELISP_NO_LENIENT=1` as comparison baselines. The
[design's performance discussion](../../design/arch/effect-concurrency.md#31-floor-scope--contention-is-the-boundary-not-compute-s94-port-finding)
records the intended floor and known contention limit.

**Inside a trace, `par-*` runs sequentially.** Trace timings include
instrumentation and do not measure ordinary parallel execution. See
[tracing](tracing.md#read-timings-as-traced-execution).

To flatten the resulting Vec of Vecs when needed, import
`collections.vec/vec-flatten`:

<!-- sample: {"kind":"repl"} -->
```
user> (import [collections.vec [vec-flatten]])
user> (vec-flatten [[1 2] [] [3]])
:(primitives/Vec primitives/Int) [1 2 3]
```

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
