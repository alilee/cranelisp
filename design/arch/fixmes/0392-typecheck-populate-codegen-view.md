---
number: 0392
target: /dev
filed_by: /arch
filed_at: 2026-06-17
sprint_filed: 84
refers_to: design/arch/concrete-boundary-type.md §2.4 (mono-population seam) / §3.0 (threading shape), crates/cranelisp-typecheck/src/traits.rs (register_mono_entry ~:1569, the mono seam ~:1508), crates/cranelisp-typecheck/src/program.rs (.ast sites), crates/cranelisp-typecheck/src/{adt,builtins}.rs
status: open
---

# Typecheck (Phase 3) — populate `ModuleEntry::Def.codegen_view` for mono instances AND concrete defns

## Issue

The concrete-boundary arc's threading shape is LANDED in `cranelisp-types`
(/arch, 2026-06-17): `ModuleEntry::Def.codegen_view: Option<MonoDefnVariant>`
(set via `DefBuilder::codegen_view(..)`). It is currently `None` everywhere —
the typecheck seam must populate it so the backend (FIXME 0391) can read it.

The transitional P2b shape pushes each instance's `MonoDefnVariant` onto a
parallel `CheckState.mono_variants` `Vec` (`traits.rs:~1517`). Under the
threading ruling that parallel `Vec` **moves onto the entry**.

## Proposed resolution

Per `design/arch/concrete-boundary-type.md` §3.0 "What populates `codegen_view`":

1. **Monomorphised instances.** At `register_mono_entry`
   (`crates/cranelisp-typecheck/src/traits.rs:~1569`, the `builder.ast(ast)` site
   ~`:1609`): hand the `MonoDefnVariant` already built at the mono seam (~`:1511`,
   currently `state.mono_variants.push(mono_variant)`) to the entry via
   `builder.codegen_view(mono_variant)`. Retire the `CheckState.mono_variants`
   parallel `Vec` (and `pass4_monomorphise`'s drain of it) once the entry carries
   the view — the view is the single source of truth (Principle 7). The mono seam
   already calls `MonoExpr::from_expr` and produces the `MonoDefnVariant`; this
   change re-targets *where it lands* (entry, not side `Vec`).

2. **Ordinary concrete defns (the non-generic case — every `Concrete{slot}`
   entry).** At each body-check `.ast(...)` site that registers a concrete
   `UserFnState::Concrete` entry — `program.rs:~2298` (multi-sig mangled), the
   single-sig body-check `.ast()` site, `adt.rs:372`/`:546` (ctors),
   `builtins.rs:708` — build the codegen view from the SAME annotated,
   subst-resolved `Defn` body via `MonoExpr::from_expr(variant.body())` and attach
   it with `.codegen_view(MonoDefnVariant { name, params, body, span })` next to the
   `.ast(..)`. Every entry that gets an `ast` AND is a codegen target (concrete,
   slotted) gets a `codegen_view`. Primitives / special forms / templates
   (`Constrained`/`Polymorphic`/`Overloaded`) get neither — `codegen_view` stays
   `None` (correct: not codegen targets).

3. **The `from_expr` failure path.** A `from_expr` error for a concrete-defn body
   (un-annotated / residual `Var` node) surfaces as the existing
   `CranelispError::TypeError` ambiguity / could-not-monomorphise error (reuse the
   §3.11.1 diagnostic wording, as the mono seam already does at `traits.rs:~1525`)
   — no new error variant, no rejection-coverage regression. For a correctly
   body-checked concrete defn this never fires.

4. **Unit tests** per CLAUDE.md §Testing: a concrete defn's registered entry
   carries `codegen_view: Some(_)` with a `MonoExpr` body; a mono instance's entry
   carries the view (off the parallel `Vec`); a template entry carries `None`; the
   `from_expr`-failure-as-ambiguity-error path for a concrete-defn body.

## Operational implication / Context

This is the population half; the backend read flip is FIXME 0391. Order: 0392
lands first (or in the same wave, populating before the read flip), so the
backend always reads a populated view. No `cranelisp-types` change (the field +
setter are landed); the typecheck `public-api.txt` is unaffected (the seam is
`pub(crate)`/internal). `CACHE_SCHEMA_VERSION` already bumped 7 → 8.
This couples with Phase-4 part A (FIXME-tracked mono-completeness): part A
ensures every minted instance is concrete so `from_expr` succeeds on every one
(the `allowed_vars` carve-out deletes) — populating `codegen_view` for mono
instances assumes part A has made them all concrete.
