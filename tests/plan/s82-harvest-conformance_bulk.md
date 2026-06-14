# S82 harvest disposition — e2e.rs + ring0.rs + ring1.rs + ring2.rs (FIXME 0134) + sketch_port.rs (FIXME 0136)

These 5 files have detailed S64 per-test reaudits. This S82 doc EXTENDS
them — it does not re-audit. It maps the S64 disposition codes onto the
S82 three-way (COVERED / GAP / OBSOLETE) and totals the measured gap.

**Code mapping (per `sprint82-test-plan.md` §2.2):**
- COVERED → **COVERED**
- DUPLICATE-IN-LEGACY → **COVERED** (the canonical legacy/active instance covers the behaviour; the duplicate adds nothing — confirm-and-drop)
- GAP-COVER → **GAP** (carry-forward not yet authored)
- GAP-HARVEST → **GAP** (crate-internal harvest)
- REGRESSION-GUARD → **GAP** (preserve; subset of GAP)

## e2e.rs (148) — FIXME 0134
Reaudit: `tests/plan/wave-5.6-e2e-reaudit.md` (File 6 totals).
- COVERED 80 + DUPLICATE 2 = **82 COVERED**
- GAP-COVER 66 (of which REGRESSION-GUARD 12) + GAP-HARVEST 0 = **66 GAP**
- **0 OBSOLETE**
- **148 tests: 82 covered / 66 gap / 0 obsolete** (reg-guard ⊂ gap: 12)
- GAP owners: src/ (slash-command arg-handling + /mod + display), backend, typecheck. int-parity shapes e2e-covered (delete).

## ring0.rs (108) — FIXME 0134
Reaudit: `tests/plan/wave-5.6-ring0-reaudit.md` (Summary).
- COVERED 99, DUPLICATE 0 = **99 COVERED**
- GAP-COVER 9 (reg-guard 4) = **9 GAP**
- **0 OBSOLETE**
- **108 tests: 99 covered / 9 gap / 0 obsolete** (reg-guard ⊂ gap: 4)
- GAP owners: typecheck (nested-if, parse-error), src/ (redefn-GOT propagation).

## ring1.rs (190) — FIXME 0134
Reaudit: `tests/plan/wave-5.6-ring1-reaudit.md` (File 7 totals).
- COVERED 136 + DUPLICATE 3 = **139 COVERED**
- GAP-COVER 51 (reg-guard 0) = **51 GAP**
- **0 OBSOLETE**
- **190 tests: 139 covered / 51 gap / 0 obsolete** (reg-guard ⊂ gap: 0)
- GAP owners: typecheck (composition shapes, spec MUST §3.8/§6.5.x/§4.4 + neg-coverage), backend.

## ring2.rs (199) — FIXME 0134
Reaudit: `tests/plan/wave-5.6-ring2-reaudit.md` (File 8 totals).
- COVERED 156 + DUPLICATE 8 = **164 COVERED**
- GAP-COVER 30 (reg-guard 7) + GAP-HARVEST 5 = **35 GAP**
- **0 OBSOLETE**
- **199 tests: 164 covered / 35 gap / 0 obsolete** (reg-guard ⊂ gap: 7)
- GAP owners: typecheck (constrained-poly, HKT, occurs-check, neg trait-impl), backend.

## sketch_port.rs (148) — FIXME 0136 (/qa-internal)
Reaudit: `tests/plan/wave-5.6-sketch-port-reaudit.md` (File 5 totals).
- COVERED 109 + DUPLICATE 5 = **114 COVERED**
- GAP-COVER 33 (reg-guard 17) + GAP-HARVEST 1 = **34 GAP**
- **0 OBSOLETE**
- **148 tests: 114 covered / 34 gap / 0 obsolete** (reg-guard ⊂ gap: 17)
- **11-known-failure lineage:** the `sigsegv_isolation_*` cluster (5
  distinct shapes), the RC cluster, and the default-method triple are
  among the 17 reg-guards. Per `sprint82-test-plan.md` §2.5: any GAP
  among the 11 historical pre-existing failures harvests as a
  **failing-not-ignored unit in the owning crate** (per
  `memory/feedback_failing_not_ignored.md`) — NOT dropped as OBSOLETE
  just because it fails. /qa performs both audit AND harvest for this
  file.

## Combined (FIXME 0134 + 0136)

| File | Tests | C | G | O | reg-guard ⊂G |
|---|---:|---:|---:|---:|---:|
| e2e.rs | 148 | 82 | 66 | 0 | 12 |
| ring0.rs | 108 | 99 | 9 | 0 | 4 |
| ring1.rs | 190 | 139 | 51 | 0 | 0 |
| ring2.rs | 199 | 164 | 35 | 0 | 7 |
| sketch_port.rs | 148 | 114 | 34 | 0 | 17 |
| **subtotal** | **793** | **598** | **195** | **0** | **40** |

## Exit checklist (per file)
- [x] (a) dispositioned (via S64 reaudit + S82 code-mapping)
- [ ] (b) GAP harvested + green (Wave 2)
- [ ] (c) files deleted (Wave 2)
- [ ] (d) README rows removed (Wave 2)
- [ ] (e) FIXMEs 0134 + 0136 closed (Wave 2)
