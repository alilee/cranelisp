> [REPL specification index](index.md)

## 7. Performance Targets

### 7.1 Startup Time [Tested tests/build_confidence::perf_simple_eval_latency_under_2000ms]

The REPL MUST start and display a prompt within **500ms** on a modern machine (defined as: Apple M-series or equivalent x86-64, SSD, 8GB+ RAM). This includes loading the prelude.

### 7.2 Expression Evaluation [Tested tests/build_confidence::perf_simple_eval_latency_under_2000ms]

Simple expressions (arithmetic, boolean logic, small function calls) MUST evaluate and display within **50ms** of the user pressing Enter. This is the combined compile + eval time. This budget holds regardless of background compilation: the scheduler's priority ladder ranks blocking REPL/typecheck work above non-blocking JIT codegen, so an in-flight prelude or module compile does not starve a trivial REPL submission. The tested latency bound (`tests/build_confidence.rs::perf_simple_eval_latency_under_2000ms`) is the normative guard; a dedicated REPL-priority work level is not required unless a regression pushes trivial-form latency past this budget under worker contention.

### 7.3 Prompt Responsiveness [R4 S10]

After displaying a result, the next prompt MUST appear within **10ms**. There MUST be no perceptible delay between result display and prompt readiness.

### 7.4 Large Output [Tested tests/build_confidence::repl_large_vec_output_bounded_under_64kb]

When displaying large values (e.g., a Vec with 1000 elements), the REPL SHOULD truncate output with an indication of the total size rather than flooding the terminal. The truncation threshold is implementation-defined but SHOULD be configurable.
