---
number: 0241
target: /arch
filed_by: /sprint
filed_at: 2026-05-30
sprint_filed: 72
refers_to: crates/cranelisp-typecheck/src/lib.rs (register_builtins re-export removed), crates/cranelisp-typecheck/src/builtins.rs (register_builtins now pub(crate) #[allow(dead_code)] legacy), design/arch/bounded-contexts.md §2 (typecheck) §7 (types) §6 (int) §4a (primitives), design/arch/decisions/0048-primitives-static-symboltable-and-got-in-crate.md, crates/cranelisp-types/src/module.rs (SymbolTable builders), design/arch/fixmes/0239-arch-instantiate-module-symbol-table-from-source-facade.md, design/arch/fixmes/0240-arch-typecheck-resolve-rename-cascade-and-module-aliases-threading.md
status: open
---

# Synthetic-module assembly leaves typecheck — SymbolTable builder vocabulary + boundary redraw (amends 0048)

## Issue

`cranelisp-typecheck` "knows the language": `register_builtins` (`builtins.rs:57`)
hand-builds the synthetic modules at session startup — special forms, intrinsic
scalar types, the `macros` module (Sexp/SList), `Option`, `IO`, `bind`, `Trace`,
`TestResult`. This is content construction, not type-checking. Typecheck's
bounded context should be: *given a set of SymbolTables populated with symbols,
annotate the types of a set of forms from a single module.* Knowing `Option`'s
field layout is outside that.

Decision 0048 already proved the target pattern for one slice: `cranelisp-primitives`
owns a static `PRIMITIVES_TABLE` that `/int` Arc-clones at startup
(`session_v4.rs:1064`), with no typecheck involvement. FIXME 0239 names the
generalization ("instantiate a module symbol table from a source"). This FIXME
records the **boundary redraw** that generalizes 0048 to *all* synthetic-module
assembly, and the **pub-interface disconnect already performed** to force it.

### Disconnect already landed (S72, the forcing function)

Per `feedback_facade_first_migration` (push the boundary to target first, accept
the broken downstream build, fix consumers wave-by-wave), the public re-export
was severed this sprint:

- `lib.rs` — `pub use builtins::register_builtins;` removed.
- `builtins.rs:57` — `register_builtins` is now `pub(crate)` + `#[allow(dead_code)]`,
  body **retained intact as the legacy assembly reference** for this migration.
- `crates/cranelisp-typecheck/public-api.txt` — regenerated; one-line diff
  (register_builtins removed).
- `cargo check -p cranelisp-typecheck --tests` green (the in-crate test fixture
  at `checker.rs:2248` reaches it via the `crate::builtins::` path, unaffected).

`int` can no longer call it. Its two call sites (`src/session_v4.rs:1072`,
`src/platform.rs:703`) are now owed migration — tracked in FIXME 0242. The break
is currently masked by `int`'s pre-existing S70/S72 `cranelisp-types` cascade
errors (import-resolution aborts before name-resolution reaches the call), and
will surface as `int` is repaired.

## Proposed resolution

`/arch` authors the Decision **amending 0048** (manifesting in `bounded-contexts.md`
§7/§2 per the manifestation-site convention — no standalone Decision file):

1. **Builder vocabulary on `cranelisp-types::SymbolTable`** — kind-shaped helpers
   (`declare_intrinsic_type`, `declare_adt`, `declare_special_form`, `declare_def`)
   that encapsulate the `ModuleEntry` shape per kind, over the existing low-level
   primitives (`new_with_params`, `insert`, `allocate_got_slot`). They live in the
   types crate (manipulate only types-crate data; multi-consumer per BC §7). This
   is the home FIXME 0239's `ModuleSymbolTableSource` concept resolves to —
   prefer a lightweight builder convention + shared methods over a trait until a
   consumer needs to be generic over sources.

2. **Relocate `register_builtins`'s body to static source builders.** Per `/arch`'s
   S72 evaluation, the user's "static builders, orchestrated by /int" framing and
   the earlier "substrate-Rust vs expressible-.cl" sketch **compose**: both tiers
   become static `SymbolTable` builders, differing only in owning crate. Bootstrap
   ordering is decisive — `macros/Sexp` references `primitives/Int`, macro
   expansion needs Sexp/SList resolvable *before the first `.cl` parses*, and IO's
   `Bind` is existential (unexpressible in HM) — so static builders are the
   default over `.cl` source for everything currently in `register_builtins`.

   Per-step classification (the 8 `register_builtins` steps):

   | Step | Disposition |
   |---|---|
   | special forms (root `""`) | substrate → static builder (metadata for `/info`) |
   | intrinsic scalars (Int/Bool/Float/String) + Vec | substrate → static builder; scalars candidate for `cranelisp-primitives` per 0239 Option A; Vec is a noted smell |
   | `macros` (Sexp/SList + sconcat) | mixed; ADT shape expressible but bootstrap-ordered → static builder, `provenance: macros` |
   | Option | expressible → static `declare_adt` builder |
   | IO (Pure/Effect/Bind) | mixed; Bind substrate → static builder |
   | bind primitive | substrate (inline CLIF) → with the externs |
   | Trace | already owned by Decision 0040 (relocates to `/int` in full) |
   | TestResult + test special forms | ADT expressible; the two fns already int-owned JIT intrinsics |

3. **`/int` orchestrates the mount** — startup mounts substrate tables → expressible-ADT
   tables → prelude `.cl`, exactly as it already mounts `PRIMITIVES_TABLE`. Reuse
   `advance_next_id_past_table` for type-var high-water monotonicity (the one
   subtlety — static builders must pre-allocate within a range or expose their
   high-water mark). Consumer-side work tracked in FIXME 0242.

4. **Typecheck deletes the legacy `register_builtins` body** once `/int` no longer
   needs it as the assembly reference (i.e., after the builders + mount land).

## Operational implication / Context

- **Sequencing: not S72.** `/arch`'s evaluation recommends S73. S72 is a
  single-crate-edge sprint (typecheck-only green; workspace-green explicitly out
  of scope) at Wave 4 (Phase B close). The redraw is inherently cross-crate
  (typecheck loses code, types gains builders, int gains orchestration). S72
  should close clean with intrinsic scalars on `IntrinsicType` (done) so this is
  a *move*, not a *rewrite*, and hand forward.
- **Blast radius is small**: one production caller (`session_v4.rs:1072`); the
  other two are test fixtures.
- **Closes FIXME 0239** (this Decision is its resolution — the facade concept +
  the generalization beyond primitives). Coordinate with FIXME 0240 (adjacent
  int↔typecheck startup-seam threading: module_aliases A1/A4).
- **Cascade inventory** (Decision-cascade discipline — same change-set when
  enacted): `bounded-contexts.md` §7/§2/§6/§4a; `facades/typecheck.md` (strike
  `register_builtins`, or its rustdoc successor if Phase C retired the facade);
  `cranelisp-types` rustdoc + `public-api.txt` (new builders); `cranelisp-typecheck`
  `public-api.txt` (already done — register_builtins removed); `cranelisp-primitives`
  rustdoc + public-api (if intrinsic scalars/bind/sconcat migrate); Decision 0048
  drain entry (generalize "primitives" → "all synthetic modules"); `interfaces.md`;
  `sequences/exec-flow-*.mmd` (startup participants — grep at enactment);
  `src/CLAUDE.md` startup notes; MEMORY.md index lines.
- Per `feedback_explicit_decision_review`: surface the Decision substance +
  rationale + alternatives to the user before cascading/enacting.
