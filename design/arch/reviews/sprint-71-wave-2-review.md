# Sprint 71 Wave 2 — `/review platform` on Phase B implementation

**Reviewer**: `/review` narrow-deployed to `cranelisp-platform`.
**Date**: 2026-05-28.
**Inputs**: 11 Wave 2 commits (`2f9b560` — `62018cf`); `design/platform/sprint71-redesign.md` (Phase A binding design); `design/arch/facades/cranelisp-platform-audit-s69.md` F1–F9; `crates/cranelisp-platform/src/{lib.rs, schema.rs, adt.rs}`; `crates/cranelisp-platform/tests/{baseline, cl_adt_products, cl_adt_sums, macro_expansion, worked_examples}.rs`; `crates/cranelisp-platform/public-api.txt`; `tests/plan/sprint71-platform.md`; `src/platform.rs` + `crates/cranelisp-exe-bundle/src/lib.rs` (int patch diff only).

## Verdict

**PASS WITH FINDINGS — apply findings then Wave 4 may begin.**

55 platform tests pass; zero new warnings; one pre-existing clippy carry (`Err`-variant-too-large on `manifest_to_descriptors`) verified S65-vintage. Architectural intent honoured across CLAdt/schema/macro/HostCallbacks/ABI_VERSION/F2-source-move. Three Important findings ride into Wave 4; four Suggestions logged.

## Departure verdicts (the four `/dev platform` flagged)

### 1. CLAdt storage convention — alloc base, not payload base. ACCEPT.

Design §5.1 contained a self-contradictory statement: "Returns the payload base pointer as i64 (NOT the alloc base — matches the `CLString` convention)" — but `CLString::as_str()` (`lib.rs:509–525`) and `From<&str>` (`lib.rs:540–561`) demonstrably store/use the **alloc base** (`payload - HEAP_HEADER_SIZE`). Wave 2 chose alloc-base, which is the actually-correct interpretation of "CLString convention." `CLHeap::raw_ptr` on `CLAdt<T>` returns the alloc base; `read_tag`/`read_field` add `HEAP_HEADER_SIZE` to reach the payload. Consistent across `lib.rs` (`from_raw` rustdoc lines 100–109; `payload_ptr` lines 112–114; `alloc_with_tag` rustdoc lines 144–158), `adt.rs` (`payload_ptr`), and the test fixtures (`cl_adt_products.rs:55–71`; `tests/worked_examples.rs:15–31`; `adt.rs::alloc_cladt_payload`).

Verdict: necessary departure, documented in the right places, no contradictions left in source. **The design doc still contains the misleading "(NOT the alloc base)" text at §5.1** — that's a design-doc bug, not an implementation bug. Logged as Important finding F-D1 below (Wave 4 fold reads design §5.1 as input; the contradiction will mislead the rustdoc author if not corrected).

### 2. `declare_platform!` `schema_types:` ident list. ACCEPT-WITH-NOTE.

`macro_rules!` cannot parse a string literal to enumerate identifiers — this is a real Rust limitation, not an implementation shortcut. The `schema_types: [Name1, Name2, ...]` ident list alongside `schema:` is the correct minimum-mechanism shape on stable Rust. Documented at `lib.rs:867–875` (the macro doc table + below-table paragraph) with the failure-mode named ("`macro_rules!` cannot parse a string-literal to enumerate identifiers") and the upgrade-path named ("a proc-macro upgrade is feasible — tracked as a future refinement").

What's missing: **the proc-macro upgrade is named as "tracked as a future refinement" but no FIXME exists.** FIXME 0234 covers the `/abi` REPL emitter (DSL → schema text); it does not cover the macro upgrade (schema text → marker-type idents). These are distinct improvements (different skill, different target).

Verdict: acceptable departure; **Wave 4 should file a new FIXME for the proc-macro upgrade** so the "future refinement" claim isn't orphaned. Logged as Suggestion F-D2 below (could be folded into existing 0234 instead of a new file; /dev or /sprint to decide).

### 3. Private `schema`/`adt` modules with crate-root re-exports. ACCEPT.

`lib.rs:14, 17` declares `mod schema;` + `mod adt;` (not `pub mod`); `lib.rs:15, 18` `pub use` the types at the crate root. Per Principle 15 (facade types live with behavior), `CLAdt`/`CLAdtType`/`Schema`/etc. are still platform-crate types; the re-export shape is a `--simplified` emission concern for `cargo-public-api`. No Principle 13 (newtype opacity) issues — `CLAdt<T>` is itself `#[repr(transparent)]` with a private `i64` field plus `PhantomData<T>`; the typedef is the contract, not the inner.

Verdict: correct call; cleaner public-api.txt emission with no semantic cost.

### 4. T25 source-text contract over `#[should_panic]`. ACCEPT-WITH-NOTE.

`extern "C" fn` panic-and-abort across FFI is the real behaviour — `#[should_panic]` cannot catch a process-exit. T25 reframed as a source-text contract test asserting "FIXME 0229", "alloc_with_tag", and "synthetic" appear in the `null_alloc_with_tag` function body (`lib.rs:1497–1520`). The rationale is documented inline in the test body.

What's missing: **no FIXME tracks the integration-time verification.** The real behaviour (panic-and-abort observed when a CLAdt::construct call lands without a wired host) is verifiable at FIXME 0229 / 0235 integration time, but no current FIXME explicitly names "verify the abort message at integration time" as an acceptance criterion. FIXME 0235 (round-trip DLL integration tests) is the natural home but currently lists only the success-path round-trips, not the gate-firing-as-expected scenario.

Verdict: acceptable interim; **Wave 4 should file a small follow-up** (or amend 0235) to capture "verify R1 gate fires with the documented message at integration time." Logged as Suggestion F-D4 below.

## Findings (additional, beyond the four departures)

### Blocker

None.

### Important

**F-D1: Design doc §5.1 contradiction on CLAdt return convention.**
Design `design/platform/sprint71-redesign.md` §5.1 (alloc_with_tag rustdoc draft) says "Returns the payload base pointer as i64 (NOT the alloc base — matches the `CLString` convention)." The implementation correctly chose alloc-base, matching CLString. The design doc's self-contradictory text will mislead the Wave 4 fold author (who reads §5.1 as input for the per-item `///` rustdoc). Filed as FIXME 0236 (target /design platform).

**F-I1: Schema parser pass-2 error loses original ParseLoc.**
`schema.rs:236–245` notes the unresolved field-type emits a synthetic `ParseLoc::start()` because the original location wasn't captured during pass-1. Comment explicitly says "we don't have the original ParseLoc by this point — emit synthetic and rely on the name for diagnostics." This is a usability issue (DLL author misspelling a field-type name gets line 1, col 1 in the error) and the comment frames it as accepted, but for a feature that just landed it deserves a FIXME so it doesn't drift into permanence. Filed as FIXME 0237 (target /dev platform; small follow-up).

**F-I2: `CLTypeWitness::from_raw_i64` for `CLString` uses unsafe transmute without SAFETY comment.**
`adt.rs:308–313` — the `impl CLTypeWitness for CLString` uses `std::mem::transmute::<i64, CLString>(raw)` with a one-line `// SAFETY:` comment "CLString is `#[repr(transparent)]` over i64; this is the standard wrap used at FFI boundaries." That's adequate; **but** `CLAdt<T>::from_raw_i64` (lines 319–321) — also a CLTypeWitness impl — calls `CLAdt::<T>::from_raw(raw)` without surfacing the same safety reasoning. The CLAdt path is safer (no transmute; just struct construction), so this is not unsound, but readers walking the file see the asymmetric explanation. Cosmetic. Filed as Suggestion F-S3 (target /dev platform; ride with the F6 fold).

### Suggestion

**F-D2 (above)**: file a FIXME for the `declare_platform!` proc-macro upgrade so the "future refinement" rustdoc claim isn't orphaned. Could fold into 0234 (target /repl) or file a new one (target /dev platform). FIXME 0238 (target /dev platform) recommended.

**F-D4 (above)**: amend FIXME 0235 to include "verify R1 gate fires with documented message at integration time" or file a separate small FIXME. Recommended: small amendment to 0235 body, no new file.

**F-S1: `CLAdt<AnyAdt>::into_typed` deferred witness check.**
`adt.rs:213–220` documents that `into_typed` defers the witness check to the first field-access call. This is reasonable (the marker change is type-system-only), but a reader expecting `into_typed` to validate at coercion time may be surprised. The rustdoc says so — adequate. Not actionable; logging here for visibility during Wave 4 fold.

**F-S2: `is_empty()` on Schema lacks coverage in baseline tests.**
`schema.rs:334–336` exposes `pub fn is_empty(&self)` but only `t18_dll_schema_lazy_static_is_reachable` indirectly exercises it (asserting `!is_empty()`). A direct unit test for the empty-schema → `is_empty()` returns true path would add ~3 lines. Not a Wave-2 blocker; logging for Wave 4 / future hygiene.

**F-S3 (above)**: harmonise SAFETY comments across the three `CLTypeWitness::from_raw_i64` impls that use unsafe.

## Standard review-area checks

**A — F2 source-move verification.** PASS. `impl Default for HostContext` deleted (`8368a7b`). Grep across workspace confirms zero callers anywhere (`sketch/cranelisp-platform/src/lib.rs:496` is the sketch oracle, out of scope). `lib.rs:692–701` retains the rustdoc paragraph documenting the F2 disposition + `#[allow(clippy::new_without_default)]`. T24 (`lib.rs:1461–1481`) guards regression via baseline scan.

**B — ABI_VERSION = 2 with bump-rules rustdoc.** PASS. `lib.rs:20–42`. Bump rules narrative correctly states: rules (i)–(iii) bump (layout-affecting / consts the DLL reads by hard-coded offset); rules (iv)–(v) do NOT bump (new wrapper variants, methods on CLAdt). History section names v1/v2 with the S71 trigger. T22 (`lib.rs:1436–1438`) pins value.

**C — Schema parser correctness.** PASS. `schema.rs`. BNF per design §1.1 — naked top-form sequence under outer `(...)`; line comments `;`; reserved set `{CLInt, CLBool, CLFloat, CLString, CLIO}` with `CLIO` rejected as both top-level and field-type. Tests T1–T8 cover well-formed product/sum/recursive/nested/polymorphic, position-tagged errors, reserved-name rejection, offset computation. Extra tests cover CLIO rejection (both paths), duplicate-type-name (with both ParseLocs), unknown-field-type, empty-schema, empty-product `(MarkerOnly ())`, comments. Pass-1/Pass-2 strategy honoured (lines 188–245). See F-I1 for the synthetic-loc carry.

**D — Marker-type infrastructure.** PASS. `adt.rs:32–55`. `CLAdtType` trait with `const TYPE_NAME`; `AnyAdt` default with sentinel `""`; `GetSchema` trait per design §7.4 option (ii); `CLAdt<T: CLAdtType = AnyAdt>` `#[repr(transparent)]` over `i64` + `PhantomData<T>` (verified by `cladt_repr_transparent_roundtrips` test: `size_of::<CLAdt<Rectangle>>() == size_of::<i64>()`). Methods match design §4: `read_tag`/`read_field`/`own_field`/`construct` on typed CLAdt; `read_tag_any`/`into_typed` on `CLAdt<AnyAdt>`. Type-witness mismatch panic format per A1 + design §3.3 (verified by T16).

**E — HostCallbacks growth.** PASS. `lib.rs:137–183`. Two new fields (`alloc_with_tag`, `validate_schema`) as raw `extern "C" fn` per Principle 14 + A6. `null_alloc_with_tag` (lines 195–208) + `null_validate_schema` (lines 215–223) implement A6 named-null pattern. R1-gate message at `null_alloc_with_tag` body contains FIXME 0229 + alloc_with_tag + synthetic-callback workaround instruction (T25 pins this). T27 confirms field-existence by structural-literal construction.

**F — `declare_platform!` macro extension.** PASS-with-departure-#2. `lib.rs:925–1024`. Two arms: Arm 1 with `schema:` + `schema_types:`, Arm 2 backwards-compat (no schema). Phase-0 schema emission per design §7.2 (lines 946–970): emits `pub struct $schema_type;` + `CLAdtType` impl + `GetSchema` impl pointing at `LazyLock<Schema>` static `DLL_SCHEMA`. F6 absorption: macro rustdoc (lines 857–924) carries the arm-shape table + below-table paragraphs explaining the schema_types redundancy + worked examples — substantive narrative present, Wave 4 has hooks to fold further. Sum-tag `#[repr(u32)]` enum emission is NOT present in the macro (design §7.2 item 4 said /design ruling "emit for sum types, skip for products" — neither path emits one currently). Filed as F-S4 (target /dev platform; cosmetic).

**G — Minimal int patch.** PASS-by-diff. `src/platform.rs:182–192` adds two named-null pointers + multi-line FIXME(0229) comment block. `crates/cranelisp-exe-bundle/src/lib.rs:94–104` same pattern. No other consequential int edits. **Workspace build not verified** per Wave 2's narrowed exit gate + FIXME 0222 (S70 typecheck cascade carry). Diff is unambiguously the documented minimum.

**H — Tests cover the plan.** PASS. 55 tests pass; planned coverage T1–T28 fully met (with T15, T17–T21 surplus split across crate-integration files). Zero `#[ignore]` per spot-grep. T23 relocated to `crates/cranelisp-platform/tests/baseline.rs` per Option A (commit `2b30415`) and refined to match landed surface naming (`HostCallbacks::alloc_with_tag` field-level path instead of crate-root). T25 reframed per departure #4.

**I — Public-API baseline.** PASS. `public-api.txt` enumerates `CLAdt`, `CLAdtType`, `AnyAdt`, `GetSchema`, `Schema`, `SchemaParseError`, `TypeShape`, `Variant`, `Field`, `FieldType`, `ParseLoc`, `CLTypeWitness`, `ExpectedFieldType`, `HostCallbacks::alloc_with_tag`, `HostCallbacks::validate_schema`, `null_alloc_with_tag`, `null_validate_schema`, `ABI_VERSION` const, F2 removal (no Default-for-HostContext line). Baseline regenerated in commit `52fe457`.

**J — F1–F9 audit absorption preparation.** PARTIAL. Source rustdoc carries substantive narrative on `ABI_VERSION` (F4-ish content), `HostCallbacks` (F4 cross-thread context), `null_alloc_with_tag`/`null_validate_schema` (R1 gate documentation), `CLAdt`/`CLAdtType`/`AnyAdt` (full design §3 narrative), `declare_platform!` (F6 partial — macro-arm table is present, F6's "internal phases" narrative absent but design §7.5 has the draft text). Wave 4 fold has hooks; design §8 mapping (F1–F9 destinations) is the binding contract for Wave 4. F1 (no `into_inner` introduced — `CLOwned` rustdoc names only `new`/`Deref`/`Drop`) ✓. F2 source-move ✓. F3 `unsafe impl Send/Sync for PlatformFn` still has the original short inline `// Safety:` comment at lines 120–122 — the expanded F3 narrative from design §8 row F3 (Principle 18 grounding + BC §5 invariant 6) is **not yet folded**. Acceptable carry to Wave 4.

**K — F5 disposition R3 honored.** PASS. `lib.rs:577–619`. `CLHeap::inc_rc` and `CLHeap::dec_rc` retained as-named (asymmetric prefix). No rename. Per R3.

**L — FIXMEs filed.** PASS. 0229–0235 all present in `design/arch/fixmes/` with correct frontmatter (number/target/filed_by/filed_at/sprint_filed/refers_to/status). Targets: 0229 /int, 0230 /frontend, 0231 /typecheck, 0232 /backend, 0233 /int, 0234 /repl, 0235 /qa. All `status: open`. Each FIXME body provides a substantive proposed resolution + operational context.

**M — Clippy.** PASS. `cargo clippy -p cranelisp-platform` returns one warning: `Err`-variant-too-large on `manifest_to_descriptors` (lib.rs:757). Git blame confirms pre-existing (S65 W1, commit `4e01cee5`, May 9 2026 — pre-S71). Carry is documented in the SPRINT.md Wave 2 outcome note. Not a S71 W2 regression.

**N — Tests are failing-not-ignored.** PASS. Spot-check via `grep -rn "#\[ignore\]" crates/cranelisp-platform/` returns no matches.

## FIXMEs filed by this review

| # | Target | Severity | Topic |
|---|---|---|---|
| 0236 | /design platform | Important | Design §5.1 contradiction on CLAdt alloc-base vs payload-base return convention (departure #1 + F-D1) |
| 0237 | /dev platform | Important | Schema parser pass-2 error loses original ParseLoc (F-I1) |
| 0238 | /dev platform | Suggestion | File a follow-up for `declare_platform!` proc-macro upgrade (F-D2) |

The two Suggestions F-S1 (deferred witness check) and F-S2 (is_empty unit test) are advisory; no FIXMEs filed. F-S3 (SAFETY comment harmonisation) and F-S4 (sum-tag enum emission absent) are cosmetic; logged here for Wave 4 awareness but no FIXMEs filed unless /dev platform wants the durable record.

F-D4's recommendation is to amend FIXME 0235's body to include "verify R1 gate fires at integration time" rather than file a new FIXME; /sprint may relay.

## Configuration consistency

The post-Wave-2 source state correctly anticipates the Wave 4 fold:

- Per-item `///` rustdoc on `ABI_VERSION`, `HostCallbacks`, `CLAdt`, `CLAdtType`, `AnyAdt`, `GetSchema`, `null_alloc_with_tag`, `null_validate_schema`, `declare_platform!` carries enough narrative that Wave 4's job is **augmentation** (per design §8 destination table) rather than rewriting. Hooks present where the fold needs to land.
- Crate-root `//!` preamble (lib.rs:1–9) is sparse — Wave 4 will add the cross-cutting Sprint 71 narrative (ABI versioning policy, CLHeap+RC discipline cross-reference, marker-type pattern intro, audience-DLL-author paragraph) here per design §8.
- `bounded-contexts.md` §5 is **not yet rewritten** — Wave 4 owns that. No partial rewrite landed in Wave 2.

One pre-fold drift to call out: the design doc §5.1 contradiction (F-D1) needs to flush before /dev folds, otherwise the per-item `///` on `HostCallbacks::alloc_with_tag` could absorb the misleading "(NOT the alloc base)" phrasing. **F-I1's resolution (FIXME 0236) is on the Wave 4 critical path.**

## Test posture

- **Pass**: 55 / 55 platform tests.
- **Fail**: 0.
- **Ignored**: 0.
- **Skipped**: 0.
- Coverage vs `tests/plan/sprint71-platform.md`: planned T1–T28 fully met. Surplus tests (RC discipline regression guards from prior sprints + Wave 2-added `cladt_repr_transparent_roundtrips`, `anyadt_read_tag_and_into_typed`, `clio_*`, `duplicate_*`, `unknown_*`, `empty_*`, `sum_variant_*`, `lookup_field_type_helper`, `variant_names_accessor`, `line_comments_*`, `worked_examples_schema_well_formed`, `null_validate_schema_returns_zero`, `t15_own_field_inc_on_read_rc_discipline`) acceptable.

## Workspace caveat

`cargo check -p cranelisp` not run per FIXME 0222 (S70 typecheck cascade carry blocks workspace build). The int-side patch (`src/platform.rs` + `crates/cranelisp-exe-bundle/src/lib.rs`) is reviewed **by-diff only**, not by-build. The diff is mechanical and unambiguous (two field-insertions + multi-line FIXME comment at each site); risk of by-diff review missing a build break is bounded.

Wave 4's facade fold + cross-reference sweep does NOT depend on a green workspace build; the fold targets source rustdoc + BC §5 + a cross-reference sweep, none of which exercise the typecheck path. Wave 4 may proceed.

## Verdict — Wave 4 may begin

**PASS WITH FINDINGS.** Apply F-I1 (FIXME 0237) and F-D1 (FIXME 0236) before Wave 4's per-item `///` fold to avoid carrying the design-doc contradiction into rustdoc. The other findings are advisory or ride with Wave 4 work naturally.
