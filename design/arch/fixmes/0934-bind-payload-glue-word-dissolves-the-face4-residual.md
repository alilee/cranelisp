---
number: 0934
target: /design
filed_by: /arch
filed_at: 2026-07-28
sprint_filed: 119
refers_to: design/arch/total-concreteness.md §3.4;
  design/backend/non-concrete-release-contract.md §4.4 (face 4's named
  bounded residual: a Pure payload nested in an unrun Bind sub-tree is not
  discharged), §5.3 (the free_io_node split this rides on);
  design/arch/fixmes/0907-* (the ruled face);
  crates/cranelisp-intrinsics/src/drop.rs (consume_io_tree / free_io_branches);
  Decision 0011 (closure DROP_GLUE_PTR — the self-description precedent)
status: open
---

# S121+: the `Pure` payload-glue word — local self-description dissolves the face-4 bounded residual

**Target: `/design`(backend) + `/design`(intrinsics), one coordinated window.
S121 or later — AFTER face 4 (S119) and the S120 ctor tranche land; the IO
node layout change is ABI-version-gated.**

Face 4's disposition (runtime-directed IO teardown) leaves one named residual:
a `Pure` node nested inside an *unrun* `Bind` sub-tree has payload type `b` —
the existential — which neither backend (no type) nor runtime (opaque word)
can name, so the payload is not discharged. `/qa`'s failing-not-ignored leak
guard carries it.

Under I-FRAME (`total-concreteness.md` §2) every IO-node construction site is
concrete post-mono: `(Pure x)` knows `x`'s concrete type; the backend's inline
`bind` lowering knows the intermediate type at each call site. So the residual
dissolves by the architecture's standing pattern (closure `DROP_GLUE_PTR`,
Decision 0011): **stamp a payload-glue word at construction** — the canonical
`drop<T>` address for the payload's concrete type — on the `Pure` node (or the
IO header uniformly; `/design` chooses the narrower sound shape), and have the
intrinsics tag-walker (`free_io_node`) call through it when discharging a
nested `Pure`. This is one glue pointer on one runtime-owned node family — the
closure precedent, NOT a general header type-word (R15 stands).

Acceptance: the face-4 residual leak guard flips GREEN and retires; no new
release identity is minted (`drop<T>` is the same canonical glue — release
contract reject criterion 5); IO node ABI version bumped in the same window.

Delete this file when the design lands.
