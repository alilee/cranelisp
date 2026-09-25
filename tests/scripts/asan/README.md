# Checking-allocator fence lane (scripted, not in nextest)

`run_fences_checked.sh` re-runs the starved-inc fence shapes under a checking
allocator. It is the checking-tool leg of QA's two-condition rule
([starved-inc fences](../../plan/s100-ownership-verification.md#32-starved-inc-fences--every-skip-the-inc-emission-site-the-s98-bug-2-class)
and [memory-safety lanes](../../plan/s100-ownership-verification.md#34-memory-safety-lanes-asanuaf-stack-slots-reuse)):
a fence counts as green only when its plain-execution leg in
`tests/ownership_fences.rs` and this leg both pass. Checking tools perturb
layout, so the behavioural legs remain the always-on guards.

- **Default leg:** the glibc checking allocator,
  `MALLOC_CHECK_=3 MALLOC_PERTURB_=42`, against `target/debug/cranelisp`.
- **Optional ASan leg:** set `CRANELISP_ASAN_BINARY` to a binary built on
  nightly with `RUSTFLAGS=-Zsanitizer=address`.
- **Verdict:** each shape runs twice via `--run`; the lane fails on differing
  exit codes or allocator abort/corruption output on stderr. Expected values
  stay in `ownership_fences.rs`.

```bash
tests/scripts/asan/run_fences_checked.sh
CRANELISP_ASAN_BINARY=path/to/asan-build tests/scripts/asan/run_fences_checked.sh
```

The script carries copies of the fence programs; update them when the
corresponding `ownership_fences.rs` templates change. Run it attended when
QA's allocation calls for the checking-tool leg; it is not run per commit.
