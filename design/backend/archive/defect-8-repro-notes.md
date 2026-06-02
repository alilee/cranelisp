# Defect 8 — `sketch_run_tests_pass_fn_called` — Repro & Diagnosis

**Workstream**: Sprint 59 B (D8)
**Co-owners**: `/backend` (primary) + `/int`
**Status**: Phase 3a — repro reduction complete; diagnosis complete; **localised fix, no design doc required**.

---

## Failure signature

Running `cargo nextest run --test sketch_port sketch_run_tests_pass_fn_called`:

```
thread 'sketch_run_tests_pass_fn_called' (739006) panicked at
  /Users/alilee/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/cranelift-jit-0.116.1/src/backend.rs:345:21:
can't resolve symbol run-test
```

Panic originates from Cranelift's JIT `finalize_definitions` step. The JIT
batch has declared `run-test` as a `Linkage::Import` symbol (because user
code in the batch calls it), but nothing registered a concrete function
pointer for it before finalize, so Cranelift panics.

**Not an IO-trampoline / RC / `bind`-over-`(IO TestResult)` problem.** The
panic fires at JIT finalize time of the `(defn count-passes …)` batch,
**before** any IO tree is constructed or the trampoline is invoked. Sprint
58's hypothesis ("latent IO-trampoline interaction with `bind` over
`(IO TestResult)`") is falsified by the stack trace.

---

## Minimal repro

The original test does four REPL evals. The failure reproduces on the
**third** one:

```cranelisp
;; Session: repl_session_with_test_prelude() — brings (import [primitives [*]])
;; from tests/fixtures/prelude.cl, so `run-test` and `discover-tests` are in scope.

(import [macros [SCons SNil]])          ;; 1. unrelated imports (no effect on defect)
(defn test-passing [] None)             ;; 2. unrelated defn  (no effect on defect)

;; 3. The failing batch — any `defn` whose body mentions `run-test` reproduces:
(defn count-passes [acc names]
  (match names
    [SNil (Pure acc)
     (SCons head tail)
       (bind (run-test head)
             (fn [result]
               (match result
                 [(TestPass n ns) (count-passes (+ acc 1) tail)
                  (TestFail n ns r) (count-passes acc tail)])))]))
;; panic: can't resolve symbol run-test
```

**Smaller still** (static reasoning — not re-run under single-test-run
policy, but follows from the code path): any `(defn f [x] (run-test x))`
evaluated at the REPL should reproduce, because it is a `TopLevel::Defn`
whose body references `run-test`, and the test-extern registration path
only triggers on `TopLevel::Expr` programs (see root cause below). The full
`count-passes` body with `bind` / `match` / `Pure` is not load-bearing for
the defect.

The same defect applies to `discover-tests` — any `TopLevel::Defn` whose
body lexically references `discover-tests` will fail finalize with
"can't resolve symbol discover-tests".

---

## Reduction journey

Started from the failing test (4 REPL evals, imports, `bind`, `match`,
`count-passes`, `my-run-tests`, evaluation). After capturing the failure
signature (single test run), reduced **by static code reading** to avoid
redundant test runs per the one-agent-one-test-run policy:

1. The panic fires at Cranelift JIT `finalize_definitions`, not at runtime.
   → The IO tree is never built; all hypotheses involving the trampoline,
     `bind`, continuation nodes, `dec_shallow_io`, or test-capture
     `print` are ruled out.
2. The panic message names `run-test` as the missing symbol.
   → Trace the registration path for `run-test` in the JIT.
3. Registration happens at `src/session_v4.rs:1609-1619` (pre-codegen
   `codegen_extra_symbols`) and `:1683-1694` (the has-expr branch's
   `jit_syms`), both gated on `program_uses_test_forms(program)`.
4. `program_uses_test_forms` at `src/session_v4.rs:1778-1787`:

   ```rust
   fn program_uses_test_forms(program: &[TopLevel]) -> bool {
       program.iter().any(|tl| {
           if let TopLevel::Expr(e) = tl {
               Self::expr_uses_test_forms(e)
           } else {
               false
           }
       })
   }
   ```

   **This only scans `TopLevel::Expr`**. `TopLevel::Defn`,
   `TopLevel::TraitImpl`, etc. are ignored. `(defn count-passes …)` is a
   `TopLevel::Defn`, so the check returns `false`, so `run-test` is never
   added to `codegen_extra_symbols`, so the JIT finalize for
   `count-passes`'s batch cannot resolve the `Linkage::Import` reference.

Reduction landed here: the bug is a plain scan gap in
`program_uses_test_forms`. No need to exercise the trampoline to repro.

---

## Hypothesis — root cause

**Localised defect**: `program_uses_test_forms` in
`src/session_v4.rs:1778-1787` is incomplete — it scans only
`TopLevel::Expr` bodies. It must also recurse into `TopLevel::Defn`
variant bodies (and, defensively, `TopLevel::TraitImpl` method bodies) so
that a `defn` whose body uses `run-test` or `discover-tests`
triggers the test-extern registration path before JIT finalize.

**Candidate fix sketch** (not to be applied in this phase):

```rust
fn program_uses_test_forms(program: &[TopLevel]) -> bool {
    program.iter().any(|tl| match tl {
        TopLevel::Expr(e) => Self::expr_uses_test_forms(e),
        TopLevel::Defn(d) => d.variants.iter().any(|v|
            Self::expr_uses_test_forms(&v.body)
        ),
        TopLevel::TraitImpl(t) => t.methods.iter().any(|m|
            m.variants.iter().any(|v| Self::expr_uses_test_forms(&v.body))
        ),
        _ => false,
    })
}
```

The symmetric `program_needs_trace` (same file, ~line 1824) has the
identical structural gap — any `defn` body containing `(trace …)` will
also fail to trigger `cranelisp_trace_format` registration. Fixing
`program_uses_test_forms` without also fixing `program_needs_trace`
would leave the parallel latent bug. The fix should touch both in one
commit (or refactor to a shared `any_expr_in_program` helper).

**Suspect code**: `src/session_v4.rs:1778-1820` (`program_uses_test_forms`
+ `expr_uses_test_forms`), and the parallel `program_needs_trace` /
`expr_needs_trace` immediately below.

---

## Design decision — localised fix, no design doc required

The repro does **not** reveal a structural problem with IO-trampoline,
`bind` over `(IO TestResult)`, continuation-produced IO nodes, shallow
decs, or the test-capture `print` argument-consumption contract. The
/arch Condition 2 invariants (i)(ii)(iii) do not apply — they guard
problems that would only surface if the trampoline were actually reached.

The defect is a plain scan-gap bug in the `/int` session's
test-extern-registration predicate. The fix is one function body (two if
we refactor the parallel `program_needs_trace` for symmetry), entirely
inside `src/session_v4.rs`, and changes no interface, no invariant, and
no primitive. It is a `/int` code change under /backend's cross-cutting
interest (since the trampoline story stays intact and the `run-test`
extern's consuming contract — which IS specified by Decision 24 — is
untouched).

No new design artefact is warranted. The existing design coverage is
sufficient:

- Decision 24 (uniform consuming convention) — unchanged; `run-test`
  extern already follows it.
- Decision 29 (`rc::dec_shallow_io`) — unchanged; the trampoline is not
  reached in this repro.
- `design/backend/io-trampoline.md` — unchanged; the fix does not touch
  the trampoline.
- `design/backend/auto-curry-and-run-tests.md` — the relevant existing
  `/backend` doc for `run-test`. A brief forward-pointer note from the
  `/int` fix commit message is sufficient for traceability.

`/sprint` can schedule this directly into the implementation wave as an
`/int`-owned fix. The ownership shifts from co-owned (`/int` + `/backend`)
to **`/int`-primary**, because the fix surface is entirely inside
`src/session_v4.rs`. `/backend` review at commit is still appropriate to
confirm the diagnosis.

---

## Out-of-scope observations (file as follow-on FIXMEs if `/sprint` agrees)

1. **Parallel latent bug in `program_needs_trace`**: a `defn` body
   containing `(trace …)` has the same registration-gap defect. Not
   currently caught by a failing test (there is no `sketch_port` or
   `wave6_demo_repros` case for "defn body with trace"). If `/qa` files
   a regression test, `/int` lands the fix in the same commit.
2. **Brittle predicate-based extern gating**: the pattern "scan the
   program AST to decide which runtime externs to register for this
   batch" has cropped up at least twice (`run-test` / `discover-tests` +
   `trace`). A more robust alternative would be to register these
   externs unconditionally for every JIT batch (they are cheap — just
   function pointers in the `JITBuilder::symbol` table). The performance
   argument for conditional registration is weak; the correctness
   argument for unconditional registration is strong. If `/arch` agrees,
   file as an S60+ simplification.

---

## References

- `tests/sketch_port.rs:1601-1643` — failing test
- `src/session_v4.rs:1609-1619, 1683-1694` — test-extern registration sites
- `src/session_v4.rs:1778-1820` — the `program_uses_test_forms` predicate (defect location)
- `src/session_v4.rs:3951-4020` — `discover_tests_extern` / `run_test_extern`
- `crates/cranelisp-typecheck/src/builtins.rs:1023-1144` — `run-test` / `discover-tests` primitive registration
- `crates/cranelisp-runtime/src/io.rs` — IO trampoline (NOT reached in this repro)
- `design/arch/CLAUDE.md` Decisions 24, 29 — NOT triggered; kept as ambient context
- `sprints/archive/sprint-58.md:706` — original re-triage hypothesis (IO-trampoline/`bind` over `(IO TestResult)`), now falsified
- `sprints/SPRINT.md` Workstream B Defect 8 + §Architecture Review Condition 2 — Condition 2 does NOT apply (no design doc needed)
