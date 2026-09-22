---
id: ACT-0983
title: Reproduce obsolete rejection of accessor-named trait methods
status: open
priority: high
from: design
to: qa
sprint: 122
filed_at: 2026-09-22
refers_to:
  - spec/07-traits.md
  - design/typecheck/fixme-0365-field-accessor-dotted.md
---

## Source-read conformance lead

The 2026-09-02 user ruling in `spec/07-traits.md` §7.3.1 permits an impl method
named like an accessor on the target type. Source still has
`check_impl_method_accessor_collisions` in
`crates/cranelisp-typecheck/src/traits/impl_check.rs`, and the four
`impl_method_colliding_*` module cases plus
`tests/spec_05_definitions.rs::impl_method_colliding_with_field_accessor_rejected_neg`
assert the old rejection. This is source-read evidence, not an executed
reproduction or a closed defect.

## QA disposition

Confirm the requirement and allocate a minimal unignored acceptance reproduction
with an ordinary non-colliding control. Design supplied this candidate:

```clojure
(deftype Box [:Int v])
(deftrait HasV (v [x] Int))
(impl HasV Box (defn v [x] 99))
```

It should register under the approved rule. Test must choose a discriminating
observation and correct superseded rejection assertions in coordination with
typecheck dev. Route the confirmed failure through the existing narrow fix
workflow; preserve module evidence and assess end-to-end coverage. Do not
reinterpret the old tests as authority over the settled requirement.

Provenance: typecheck design session `55417728-1ee9-4ced-bd78-a191dde9e101`.
