---
number: 0351
target: /typecheck
filed_by: /sprint
filed_at: 2026-06-14
sprint_filed: 82
refers_to: tests/spec_08_modules.rs (super_import_resolves_parent_type_constructor — match workaround), tests/plan/ledger.md (S82 entry), spec/05-definitions.md §5 (field accessors), spec/08-modules.md (self-qualified type refs), crates/cranelisp-typecheck/src/resolve.rs
status: deferred
deferred_at: 2026-06-14
deferred_reason: tangential pre-existing defects discovered late in S82 while repairing the 0342 ctor test fixture; the 0342 guard is green via a match-based workaround; these two are out of S82's committed scope
target_sprint: 83
---

# Two pre-existing typecheck defects surfaced while repairing the 0342 ctor fixture

## Issue (S82 /qa finding)

While fixing the invalid postfix-annotation fixture for `super_import_resolves_parent_type_constructor`, `/qa` found two independent pre-existing defects, both reproducing in a SINGLE file (not super-import-specific):

1. **Field-name accessor is not a free callable.** `(deftype Box [:primitives/Int v])` should auto-generate an accessor `v` (spec §5: accessor = field name), but `(v b)` errors `undefined variable: v`. (The original fixture's `box-v` was wrong; the real accessor name is the field name `v`, and even that does not resolve as a free callable.) **First confirm the spec semantics** — does Cranelisp auto-generate field accessors as free functions? If yes, this is a typecheck/resolution defect; if the accessor is meant to be reached only via pattern `match`, this is a fixture/expectation issue and the FIXME closes as not-a-defect. (`/spec` arbitration may be needed before the typecheck fix.)

2. **Self-qualified type reference fails.** `:superp/Box` referenced INSIDE `superp.cl` (or `:t/Box` inside `t.cl`) errors `unknown type \`X\` (from module \`\`)`. A module should be able to reference its own types by their fully-qualified name. This is a typecheck/resolution defect.

The 0342 ctor guard is green via a `match`-based field extraction workaround (avoids the accessor) — so neither of these is a red guard; they are documented debt.

## Proposed resolution

Per the user-proxy defect protocol, `/qa` authors narrow failing-not-ignored repros for both (single-file, no super-import). Then `/typecheck` resolves (1) after the spec-semantics confirmation and (2) the self-qualified resolution. `// spec:` → spec/05-definitions.md §5 (accessors) + spec/08-modules.md (self-qualified type refs).

## Context

S82 Workstream D. Tangential to the 0342 super-import fix (which is complete). Deferred to S83 with failing repros owed (the repros fold into the S82 harvest /qa pass if convenient, else S83 opening). Durable record: `tests/plan/ledger.md` S82 entry.
