# ASan / checking-allocator lane (scripted, NOT canonical nextest)

The two-condition rule (`tests/plan/s100-ownership-verification.md` §3.2):
every starved-inc fence and memory-safety lane runs under plain execution
(the canonical `tests/ownership_fences.rs` behavioral+balance legs) AND under
a checking tool. A fence green only under one condition is not green
(`memory/feedback_verify_fix_not_symptom_absence.md` — tools perturb layout;
the behavioral legs are the always-on guards).

**Toolchain reality on this platform (aarch64 Linux, honest cap per §3.4):**
ASan needs `RUSTFLAGS=-Zsanitizer=address` on nightly with a rebuilt binary;
where unavailable, the documented fallback is the glibc checking allocator:
`MALLOC_CHECK_=3 MALLOC_PERTURB_=42`.

Run at B3 wave gates (attended), not per-commit:

```bash
tests/scripts/asan/run_fences_checked.sh          # checking-allocator lane
CRANELISP_ASAN_BINARY=path/to/asan-build \
  tests/scripts/asan/run_fences_checked.sh        # true-ASan lane (optional)
```

The script re-runs the fence corpus (`ownership_fences.rs` fixtures via
`--run`) under the checking allocator and fails on any abort/crash. Scope
grows with the B3 mechanisms (stack slots → L-C2 shapes at ≥10k iterations;
reuse → L-C3 at increment II).
