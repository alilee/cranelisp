---
number: 0489
target: /qa
filed_by: /sprint
filed_at: 2026-07-01
sprint_filed: 97
refers_to: tests/concurrency_v9_abi.rs (2.1), tests/concurrency_fanout_web.rs (5.1B idle_armed_server_survives_then_serves), design/arch/effect-concurrency.md §4.1.1 (tramp-opacity ruling)
status: open
---

# Two S97 v9 test-side residuals — 2.1 reframe (invalid guard) + 5.1B timing margin

## Issue

1. **2.1 `connection_opaque_field_present_but_not_user_destructurable_neg` is an INVALID guard — reframe it.** /arch ruled (S97) that `Connection` opacity is to the **trampoline, not the user**: the user CAN read/destructure their connection's genuine `fd` field (`(match c [(Connection f) f])` typechecks — correct, not a bug). So 2.1 asserts a **non-invariant** and stays RED forever against correct code. **Retire it; invert to a positive `connection_field_user_readable`** (destructure yields the real fd → GREEN). Optionally add `fabricated_connection_errors_safely_no_ub` (a user-built `(Connection 999)` passed to `read-conn` → recoverable EBADF-class error, no host UB — per the §4.1.1 fabrication ruling; needs a platform IO-error fixture). The true scheduling-opacity invariants are already covered by 2.5 (`carries_no_scheduling_state`) + the backend CLIF-absence unit.

2. **5.1B `idle_armed_server_survives_then_serves` — timing-margin miss (RED, not a mechanism defect).** The 0479 armed-ness detector + `drive_mode`/backstop mechanism is correct (5.2 + Case-A green); 5.1B fails by a ~0.1s margin because the `web_fanout` fixture's `bind-listener`+JIT startup pushes the scaled backstop fire to ~4.2s vs the test's ~4.1s check. **Widen the idle window** (or coordinate with /port to speed fixture startup) so the witness fits the suite-time budget without a real 30s wait.

## Proposed resolution

/qa: reframe 2.1 (retire→invert) and widen 5.1B's idle window. Both are test-shape corrections on correct mechanisms; the current REDs are the records.
