---
number: 0633
target: /qa
filed_by: /sprint
filed_at: 2026-07-17
sprint_filed: 111
refers_to: crates/cranelisp-backend/src/compiler/resolution.rs:117 (adt_drop_glue_name);
  vec_codegen.rs:819-864 (concrete_args field classification) + :870 (get_name skip);
  resolution/tests.rs::adt_drop_glue_naming_identity_is_fqtn_keyed;
  S111 CS-1 /review finding I1 (backend review of 522c66e5)
status: open
---

# ADT drop-glue name under-keys (bare `fqtn.name` only) — latent 0350/ledger-25 silent-mis-drop class, and CS-1 canonized it as correct

## The defect (latent, pre-existing, but newly ASSERTED-away by CS-1)

`adt_drop_glue_name` keys the drop-glue symbol on `fqtn.name` **alone** — dropping
both the **module** and the **concrete type args** — while the glue BODY depends on
the instantiation's per-field heap categories (`vec_codegen.rs:819-864` substitutes
`concrete_args` before classifying heap-ness), and the `get_name` skip (`:870`) hands
the first-built glue to any later same-named type in the compiling module.

Collision cases (each → wrong field decrements: dec a non-pointer, or skip a heap field):
- two mono instantiations `(Pair Int Str)` vs `(Pair Str Int)` (concrete-args axis);
- two bare-same-name ADTs from different modules used in one compiling module (module axis).

This is exactly the **0350 / ledger-25 silent-mis-drop class** that S111 R6 (drop-glue
discipline) exists to cure — recurring on the name×instantiation and name×module axes.
Byte-identity is unaffected (the old inline `format!` keyed identically), so CS-1 did
not regress it — BUT CS-1's new rustdoc + `adt_drop_glue_naming_identity_is_fqtn_keyed`
now **assert** "per-TYPE keying ⇒ the collision class does not apply" (the test even pins
`"runtime/drop_glue_Box"` with the module dropped). **Shipping a false regression guard
that masks a real defect is itself a defect** — this must not stand into Phase-6.

## Requested action

`/qa`: assess reachability and produce (or direct `/testing` to produce) a **minimal repro**
per `tests/CLAUDE.md` §"Isolating Cross-Crate Failures" — does monomorphisation naming
actually let two heap-category-divergent instantiations reach `adt_drop_glue_name` with the
same bare name in one compiling module? A failing-not-ignored repro is the record + trigger.

Then the layered handoff:
- **/dev (backend)** — correct the false rustdoc + test assertion NOW (do not assert a
  collision-freedom the key does not deliver); if the repro confirms reachability, re-key
  the glue name on module + concrete-args (the honest fix R6's discipline implies).
- **/design (backend)** — the canonized design claim in `audit-drain-s111.md §4` / crate
  rustdoc needs correcting to match the real keying discipline.

Fix-vs-carry is `/sprint`'s call once the repro lands: if cheap + reachable, a CS-1.1
corrective this sprint; else correct the false assertion + carry the re-key with the
committed failing repro as the durable trigger.
