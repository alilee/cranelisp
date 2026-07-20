---
number: 0701
target: /testing
filed_by: /dev
filed_at: 2026-07-20
sprint_filed: 114
refers_to: tests/repl_persist.rs::persist_type_decl_regen_preserves_source (line ~1387); crates/cranelisp-frontend/src/ast_builder.rs::build_constructor_def (S114 W-D1 deftype-ctor trailing reject)
status: open
---

# Corpus casualty: `persist_type_decl_regen_preserves_source` uses an invalid two-bracket ctor

The S114 W-D1 deftype-ctor trailing-form fix (flipping the pre-existing RED
`tests/spec_05_definitions.rs::deftype_ctor_trailing_form_after_field_bracket_rejected_neg`;
`design/frontend/enforcement-matrices.md` §2) makes `build_constructor_def`
reject **any** form after a valid `[:Type name]` field bracket — a constructor is
`(Name [:Type name …])` with a SINGLE field bracket (spec §5.2 grammar).

`tests/repl_persist.rs::persist_type_decl_regen_preserves_source` seeds:

```
(deftype Pt (MkPt [:Int x] [:Int y]))
```

This is an **invalid** two-bracket spelling. On HEAD it "worked" only because the
constructor parser silently DROPPED the second bracket (`[:Int y]`) — the exact
silent-accept defect the W-D1 fix closes — so `MkPt` was registered as a
one-field ctor and the deftype regenerated. With the fix, `(MkPt [:Int x] [:Int y])`
is now correctly rejected ("constructor `MkPt` has an unexpected trailing form
after its field list"), so the `deftype` never registers and is absent from the
regenerated `user.cl` → the test reds.

**This is a fixture-syntax casualty, not a regression** — the fix is exactly what
the acceptance RED and the design demand. The test was NOT a baseline RED (it
passed on HEAD `58ac8e46`), so it needs the fixture corrected in the SAME wave as
the flip (the corpus-sweep-with-fix discipline, `binder-head-reject.md` §7,
applied to the BD-A2/deftype-ctor family).

**Fix**: change the seed to the valid single-bracket two-field product ctor —
`(deftype Pt (MkPt [:Int x :Int y]))` (the canonical form, cf.
`spec_05_definitions.rs` `(deftype Point [:Int x :Int y])`). The test's assertion
(regen preserves `deftype`/`Pt`/`MkPt`, §5–7 regen fidelity, FIXME 0538) is
unaffected — only the ctor spelling was malformed.

`/dev`(frontend) cannot edit `tests/` (that is `/testing`'s). Filed so the
one-line fixture correction lands and the test flips green. `/qa` may also want
to note the deftype-ctor trailing flip against the S114 corpus sweep.
