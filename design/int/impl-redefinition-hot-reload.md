# Impl-redefinition is hot-reload — the mangled method Defs must re-enroll (S115, FIXME 0714 / spec §5.4.5)

> Subordinate topic doc, cited from `design/int/int.md` and the `session-transaction.md`
> redefinition family. Owned by `/design`(int). Authored S115 Phase 3 against
> SPRINT.md §Scope-A "/dev(src): impl-redefinition hot-reload ×1", the /arch
> Phase-2 §5 ruling, spec `05-definitions.md` §5.4.5 [S115], and the polarity-safe
> pin `tests/impl_redefinition_dispatch.rs`.
>
> **Status: DESIGN, pre-implementation.** The fix is src-internal; NO cache/schema
> edit, NO `cranelisp-types` edit, NO impl-specific parallel path (P11).

## 0. The defect, in one line

Re-`impl`ing a trait for the same target type in one live session is **silently
ignored**: the second `(impl Sizeable Box (defn size [x] 7))` prints the ordinary
confirmation, yet dispatch keeps running the **first** impl's body (`12`, not `7`)
— the new method body never recompiles. Spec §5.4.5 [S115]: *"An implementation
MUST NOT silently ignore a re-`impl`."* User ruling (S114 close): the required
behavior is **hot-reload** — a same-type re-impl **takes effect**; a
type-changing re-impl **rejects** (defn's §18 rule).

## 1. The actors and the function between them (Principle 21)

A trait `impl` is compiled as a set of **mangled method `Def`s** — `size` becomes
`Sizeable.size$user/Box` (`mangle_trait_method`; the `$Type` suffix is the FQ impl
type). Those mangled Defs are the **callables** trait dispatch (§7.4) resolves
through the GOT. On registration (`crates/cranelisp-typecheck/src/traits/impl_check.rs`):

- the **`TraitImpl` shell** (the discovery record) is written to the **trait's
  home** module via `.insert` (`impl_check.rs:377` — an overwriting insert, so a
  re-impl already replaces the shell), keyed `impl$<fqType>$<fqTrait>`, carrying
  `impl_module = state.current_module` (D45/S110 W0.1: the shell lives at the
  trait's home, the mangled method `Def`s live in the **writer's** module,
  `impl_check.rs:387`);
- each method body is type-checked against the instantiated trait signature and
  written as a mangled `Def` (`ast: Some`) in the writer's module
  (`check_impl_method`).

The **missing function** is *"a re-impl's new method bodies reach the GOT-patch
that every other redefinition already uses."* They do not — because of the
codegen-batch enrollment gap below.

## 2. The silent-ignore locus (found; cited)

**`src/worker.rs::derive_codegen_batch`** builds the per-turn set of symbol names
to (re)compile. It has two loops:

1. a **forced** first loop over `program` (`worker.rs:966–1001`) — `try_push`
   enrolls a name whenever the live table has a `Def { ast: Some, .. }` under it
   (excluding constrained/polymorphic/overloaded templates). This loop does **NOT**
   consult `code`/`already_compiled`, so a redefined entry with carried-over code
   is still enrolled and recompiled — **this is how `defn` hot-reload works**;
2. an **uncovered-sibling sweep** (`worker.rs:1003–1021`) over the remaining
   `defined_symbols()`, which **skips any entry whose live `code.is_some()`**
   (`already_compiled`, `:1012–1019`).

The `TopLevel::TraitImpl` arm of the forced loop (`worker.rs:994–997`) enrolls the
**unmangled** method name (`size`) — a **dead lookup**: there is no live `Def`
named `size` (the callable is the mangled `Sizeable.size$user/Box`), so `try_push`
misses. The impl's actual mangled method Defs are therefore reachable **only via
the sweep**, which is `already_compiled`-gated.

The failure chain on re-impl:

1. the new mangled Def is staged with `code: None` (staging never runs codegen)
   and committed by `worker::commit_staging_to_live` → `commit_slotted_def`;
2. `commit_slotted_def` classifies the redefinition **AbiPreserving** (same trait
   signature ⇒ same ABI) and **carries over the prior compiled code**
   (`worker.rs:621–623`), so the freshly-committed live mangled Def now has
   `code: Some(<first impl's code>)`;
3. `derive_codegen_batch` runs: the forced arm's unmangled `size` push misses; the
   sweep sees the mangled Def `already_compiled` (`code: Some`) → **skips it**;
4. the new body (`7`) never recompiles; the GOT slot keeps the first impl's code;
   dispatch returns `12`. Silent ignore.

> **Locus:** `src/worker.rs::derive_codegen_batch` `TopLevel::TraitImpl` arm
> (`:994–997`, unmangled-name dead lookup) × the `already_compiled` sweep gate
> (`:1012–1019`), given the AbiPreserving code carry-over at
> `commit_slotted_def` (`:621–623`). `// defect: class=silent-accept
> locus=src/worker.rs::derive_codegen_batch found=S114 owner=/dev`.

## 3. The fix — enroll the mangled method Defs (P11: the SAME path as defn)

Change the `TopLevel::TraitImpl` arm of `derive_codegen_batch` to enroll the
impl's **mangled method Defs** into the **forced** first loop, exactly mirroring
the multi-sig `defn` arm that already enrolls `base$…` mangled variants
(`worker.rs:971–989`):

- for each `method in impl_.methods`, enroll every live `defined_symbols()` entry
  whose name is the method's mangled form — `{impl_.trait_name}.{method}$…`
  (split on the last `$`; prefix `{trait}.{method}`). This is the /dev mechanism;
  the **binding contract** is: *every mangled method Def of the impl enters the
  forced batch* (so the sweep's `already_compiled` gate no longer governs whether
  a re-impl recompiles).

Because the forced loop ignores `already_compiled`, the re-impl's carried-over-code
mangled Def is re-enrolled → codegen recompiles its new body → `commit_slotted_def`
had already reused the **same GOT slot** (AbiPreserving) → the slot is patched in
place → dispatch resolves the **new** body. This is byte-for-byte the mechanism a
redefined `defn` already uses; **no impl-specific commit path is created**
(P11/P7). First-impl behavior is unchanged (code `None` → compiled either way; the
former dead unmangled push did nothing).

The **only** impl-specific residue (per /arch §5) is what already exists: the
`TraitImpl` shell overwrite at the trait's home (`impl_check.rs:377`, an
overwriting insert) + the mangled method Def re-staging (`check_impl_method`).
Both already happen on re-submission; neither is new.

## 4. The same-type constraint needs NO new src gate — it is inherited

Spec §5.4.5 / §18: a re-`impl`'s methods MUST conform to the trait's declared
signature; a non-conforming re-impl is rejected exactly as any non-conforming
impl. This is **already enforced**, at two existing seams — the fix adds none:

1. **Conformance / rejection** — `impl_check.rs` type-checks every method body
   against the instantiated trait signature (`check_impl_methods_present` +
   `check_impl_method`) **before** any commit. A body that does not conform is
   rejected there with nothing staged — identical to a first impl. Because the
   **trait signature is fixed**, every *conforming* re-impl is **signature-
   preserving** by construction (spec §5.4.5: *"leaves each method's compiled
   signature unchanged … signature-preserving"*).
2. **ABI classification** — `commit_slotted_def`'s `classify_redefinition`
   (`worker.rs:556–568`) is the same authority `defn` redefinition uses. A
   signature-preserving re-impl classifies **AbiPreserving** → same slot re-pointed
   → cross-module compiled callers stay valid by construction (D35: the GOT is the
   single source of truth for callable addresses). No epoch/freeze machinery
   engages (that is the `AbiChanging` arm, which a fixed-signature re-impl cannot
   reach) — so ownership-summary skew is not widened beyond defn's existing
   exposure (/arch §5); the S5 dependent-recompilation transaction remains the
   R12-sprint answer, untouched here.

So the "same-type constraint at the impl registration seam" is the **conjunction
of the existing trait-conformance check and the existing `classify_redefinition`
gate** — the §18 defn rule applied at the impl seam, with no new predicate. (A
type-changing re-impl is rejected at seam 1; it never reaches seam 2.)

## 5. Testability (Principle 5) — the unit tier

- **Unit (mandatory, at the src seam)**: drive `derive_codegen_batch` (or the
  eval-turn recompile chain) for a re-impl and assert the mangled method Def is
  **enrolled** (fail-on-revert: the pre-fix batch omits it). This pins the exact
  seam the bug lived at, independent of the e2e dispatch outcome.
- **e2e (the /qa pin)**: `tests/impl_redefinition_dispatch.rs::reimpl_either_dispatches_new_or_notices_not_replaced`
  is the polarity-safe RED; at flip, /testing sharpens it to the ruled branch —
  after a same-type re-impl, `(size (Bx 0))` dispatches the **new** body
  (`:primitives/Int 7`), retiring the "notices not replaced" alternative arm
  (SPRINT.md §1.6). A type-changing re-impl e2e negative (reject, not silent
  confirm) exercises the inherited seam-1 rejection.

## 6. Sequencing (binding, /arch §5 + §8)

- **/spec 0714 scribes FIRST** — landed (spec §5.4.5 [S115]); the pin's `// spec:`
  anchor now resolves to spec text.
- **0604 early wave lands BEFORE this fix** — both are /dev(src) and touch the
  same `src/worker.rs` commit seams (`commit_staging_to_live`); 0604 goes first
  (/arch sequencing item 3). This doc's fix is downstream of the 0604 predicate
  change and independent of it (different function — `derive_codegen_batch` vs the
  `commit_staging_to_live` gate call).

## 7. Principles cited

- **Principle 11 / Principle 7** — the impl-redefinition routes through the SAME
  redefinition commit path as `defn` (`commit_staging_to_live` →
  `commit_slotted_def`); a parallel impl-specific commit/recompile path is a
  REJECT. The fix is a one-arm enrollment correction that lets the impl reuse the
  existing GOT-patch machinery.
- **Principle 18** — the mangled method Defs are enrolled structurally
  (mangled-name match), mirroring the multi-sig variant enrollment; no
  name-privileged special case.
- **Principle 20 (D35)** — the same-slot GOT-patch keeps mixed-ABI edges
  unrepresentable; signature-preservation is what makes AbiPreserving correct.
- **Principle 5** — the enrollment gap is unit-testable at the `derive_codegen_batch`
  seam without an e2e session.

## 8. Cross-references

- `spec/05-definitions.md` §5.4.5 [S115] — the hot-reload/same-type/silent-ignore
  ruling this designs to; `spec/07-traits.md` §7.3 (impl registration).
- `src/worker.rs` — `derive_codegen_batch` (the silent-ignore locus, §2),
  `commit_staging_to_live`:439 / `commit_slotted_def`:543 (the GOT-patch path the
  fix reuses; carry-over at :621–623; `classify_redefinition` at :556).
- `crates/cranelisp-typecheck/src/traits/impl_check.rs` — the shell insert (:377,
  overwriting), `impl_module` (:387), method-body conformance check.
- `src/redefine.rs` + `design/int/session-transaction.md` — the redefinition
  machinery (`RedefKind`/`RedefinitionOutcome`); this doc is the impl-variant note.
- `tests/impl_redefinition_dispatch.rs` — the polarity-safe pin; SPRINT.md §1.6 +
  `tests/plan/s115-test-plan.md` §1.6 — the wave acceptance.
- `design/arch/backend-keyed-consumer.md` §1.1.1 (D45 method co-location amend) —
  why the shell lives at the trait's home and the mangled Defs at the writer's.
