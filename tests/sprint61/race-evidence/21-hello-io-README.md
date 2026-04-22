# 21-hello-io evidence — Sprint 61 Wave 4 step 4b

**Frozen artefacts** supporting Slice 4 step 4c hypothesis selection
(separate agent). Captured at SHA `776a6cf`. Do NOT overwrite when the
fix lands — post-fix dumps go under `21-hello-io-post-fix-<SHA>.log`.

## Summary

The target defect is `examples_run::every_example_file_runs_under_examples_prelude`
as it drives `examples/21-hello-io.cl` to exit 201 under stress. S61 Wave
1 discovered that under `CRANELISP_IO_TRACE=1`, the subprocess SIGABRT/
panics in `cranelisp_run_io: unknown IO tag N` where `N` is a
near-garbage i64 — memory-corruption / type-confusion signature, not a
concurrency race.

Reduction (step 4a) confirmed the failure reproduces **standalone,
100% rate, ~no concurrency dependency**. The concurrency-shape narrative
(H(4-2) stdio DLL buffer ordering, H(4-3) nextest crosstalk) is therefore
not supported — evidence points at **H(4-1) IO trampoline continuation
handling**.

## Harness

All dumps were captured standalone:

    cd examples
    CRANELISP_IO_TRACE=1 RUST_BACKTRACE=1 \
      target/debug/cranelisp --run <file.cl> </dev/null 2>&1

Exit codes observed on 30 standalone iterations of the full
`21-hello-io.cl`:

    | code | count | meaning                                          |
    |------|-------|--------------------------------------------------|
    | 133  |  73%  | SIGTRAP — Rust panic aborted mid-print           |
    | 201  |  13%  | i32 truncation of an abort-status int            |
    | 101  |  13%  | Clean Rust panic with backtrace on stderr        |

Under 6-thread concurrent spawn (5 rounds × 6 processes = 30 procs):
same 73/13/13% distribution. Concurrency does not change the rate.

The different exit codes all trace to the same root bug: the
trampoline panics on an unknown IO tag. The exit code varies because
macOS FD/buffer handling of stderr during abort/panic sometimes
truncates the panic message, sometimes delivers it, sometimes
escalates to SIGTRAP from inside signal handlers. Exit 201 = one
specific case of panic-abort i32-truncation; Sprint 60 Defect 2 is the
same bug as the three Slice-0 observability-test failures.

## Runs

### `21-hello-io-failing-776a6cf.log` (121 lines)

Captured from the 8-test reduced variant of `main` that drops part 7
(platform IO) from `21-hello-io.cl`. Proves **the stdio platform DLL
is NOT required to reproduce** — H(4-2) is not supported.

Sequence: 11 valid BindEnter/ContPush/PureStep/ContPop/BindExit cycles
traverse the main's test-fn chain. Last valid event: `BindExit
new_current=0xa56c89260`. The trampoline then reads from `0xa56c89260`,
gets tag `435744236914` (garbage), panics at `io.rs:326`.

Suspicious: `0xa56c89260` was **previously used as a cont pointer** at
ts=48000 (`ContPush cont=0xa56c89260`) and consumed at ts=48459
(`ContPop cont=0xa56c89260`). The closure's code_ptr at
offset 16 is being (mis-)read as the IO tag.

### `21-hello-io-failing-min-776a6cf.log` (36 lines)

**Minimal repro** — 7 source lines, 100% crash rate:

    (import [primitives [Pure bind]])

    (defn then [a b]
      (bind a (fn [_] b)))

    (defn test-then []
      (bind (then (Pure 999) (Pure 42))
        (fn [x] (Pure (add-i64 x 8)))))

    (defn main []
      (bind (Pure 1) (fn [r1]
        (bind (test-then) (fn [r2]
          (Pure (add-i64 r1 r2)))))))

10 IO trace events, then panic: `unknown IO tag 6578533` at `io.rs:326`.
Final valid event: `BindExit new_current=0xb0f0acf60`. That pointer
has not been seen as any previous `inner=` or `cont=` value directly,
but lies in the same heap region as `cont=0xb0f0acf40` (ts=18667) and
`inner=0xb0f0acfc0` (ts=19125).

Shrinking further (dropping either the outer `(bind (Pure 1) ...)` or
the outer `(bind (test-then) ...)` wrapper, OR inlining `then` so no
user function wraps `(bind a (fn [_] b))`, OR replacing `then` with a
2-arg fn that doesn't construct a bind, OR using 0-arg IO-returning
user fn) ALL yield clean runs. The crash therefore requires a
**user-defined fn whose body constructs a `(bind x (fn [_] captured-IO)) `
Bind node** called from inside an outer trampoline continuation.

### `21-hello-io-passing-776a6cf.log` (68 lines)

Captured from a 5-test reduced variant of `main` (tests 1-5 only — all
return from `Pure`-only chains, no higher-order combinators). Exits
cleanly at `TrampolineExit result=175`. Proves the trampoline itself
walks 10+ binds without issue when no HOF like `then`/`map-io` is
involved.

## High-level divergence signature

| Aspect            | Passing                          | Failing                        |
|-------------------|----------------------------------|--------------------------------|
| Tail event        | `TrampolineExit result=N`        | panic `unknown IO tag N`       |
| Last BindExit     | points at Pure node              | points at previously-seen cont |
| Test main uses    | test-pure-int/bool/simple/chain/multi-ref | ...+test-then (uses HOF `then`) |
| Process exits     | `TrampolineExit`+clean i32       | SIGTRAP (133) / i32 abort (201) / panic (101) |

The single variable that flips the sign is whether `main` calls an
IO-returning user fn that itself constructs a Bind over a captured IO
parameter. This is a **closure-parameter-vs-IO-node type confusion**
or a **fresh-Bind RC-accounting leak** — see
`design/backend/slice-4-21-hello-io-investigation.md` for the
hypothesis discrimination.

## Passing-run caveat

The "passing" dump is from a structurally different program — Part 7
(platform IO) AND `test-then`/`test-map-io` are removed from `main`.
We cannot get a passing dump from the same source as the failing
one because the failing source fails 100% of the time. This is
evidence FOR hypothesis H(4-1), not a limitation: the reproduction is
deterministic at ≥99% once the bug-triggering construct is present.

## Reproduction

Failing (100% rate):

    cd examples
    cat > __bug.cl << 'EOF'
    (import [primitives [Pure bind]])
    (defn then [a b] (bind a (fn [_] b)))
    (defn test-then [] (bind (then (Pure 999) (Pure 42)) (fn [x] (Pure (add-i64 x 8)))))
    (defn main [] (bind (Pure 1) (fn [r1] (bind (test-then) (fn [r2] (Pure (add-i64 r1 r2)))))))
    EOF
    CRANELISP_IO_TRACE=1 RUST_BACKTRACE=1 \
      ../target/debug/cranelisp --run __bug.cl </dev/null 2>&1 | head -40

Expect SIGTRAP or panic with `unknown IO tag`.

## Scope

- Frozen. DO NOT overwrite at step 4e fix.
- Step 4c (hypothesis selection by /arch) reads these + the design
  doc and picks H(4-1)/(4-2)/(4-3).
- Step 4e (fix) leaves these intact; post-fix dumps go under
  `*-post-fix-<SHA>.log`.
