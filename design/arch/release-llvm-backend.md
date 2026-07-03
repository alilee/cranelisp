# The Release Efficiency Tier (`--release`)

**Status:** DESIGN PROPOSAL (Phase H) — pre-implementation, pre-user-ratification.
**Owner:** `/arch`.
**Scheduling:** Phase H (`sprints/ROADMAP.md` row H — GATED behind the S86→S87 pre-H consolidation arc + the pre-H scope-decision gate). This document is an *input* to that gate, not a green light.
**Provenance:** Authored across three `/arch` design passes during S86 (main design → closed-world-optimizations addendum → encapsulation/facade-impact revision) and consolidated here. The encapsulation revision **supersedes** the earlier "new `cranelisp-backend-llvm` crate" and "extract analyses above the backend" recommendations; this document reflects the final decisions.

---

## §0. Context and scope

Cranelisp ships two codegen *cardinalities* over **one** Cranelift codegen path: `compile_to_module::<JITModule>` (REPL / `--run`, per-symbol) and `compile_to_module::<ObjectModule>` (`--link`, per-module → `.o` → system linker → standalone exe). The full pipeline — frontend → typecheck → **monomorphisation** → RC insertion → codegen — is stable and green (S85: `--workspace` 2752/0; S86: 2812/0). The long internal-refactoring run is behind us; Phase H is the first genuinely-new-capability work.

This document designs `--release`: **the tier for final runtime space and time efficiency.** The headline framing (§2) is deliberate: `--release` is *not* "the LLVM backend" — it is an **efficiency tier** of which LLVM codegen is one component, alongside GOT-elision/direct-calls, whole-program optimization (LTO), and beyond-RC memory management.

The performance motivation is concrete: the Sudoku exemplar — the S86 showcase centerpiece — solves an *easy* 9×9 in **~3.3 s** on the debug Cranelift backend, "minutes" for hard puzzles (FIXME 0408). FIXME 0408 names two compounding causes: the copy-per-edit grid (a representation fix) **and** "the unoptimized debug backend (no release/Tier-2 backend until Phase H)." This tier addresses the second — and, via Perceus-style reuse (§8), contributes to the first.

---

## §1. Goals and non-goals

### 1.1 Goals
- **G1 — Optimized native executable.** `cranelisp --release <entry>` produces a standalone, stripped binary equivalent in *shape* to today's `--link` output (single exe, static runtime bundle, statically-linked platform rlibs, no `dlopen`) but built through the efficiency mechanisms (§6) + LLVM `-O2`/`-O3` + LTO.
- **G2 — Realistic speedup.** 3–10× over debug Cranelift on numeric/allocation-light loops; ~1.5–3× on allocation-heavy code (the Sudoku copy-per-edit shape) until the representation fix lands. **Honest framing:** the LLVM constant-factor is a *compounding* win, not a substitute for the FIXME-0408 algorithm/representation work — but the beyond-RC mechanisms (§8) *do* attack the allocation count algorithmically.
- **G3 — Zero language-semantics change.** `--release` is a pure efficiency-tier swap below the `MonoExpr` boundary. No language behaviour, observable output, or type rules change.
- **G4 — Dev loop unaffected.** Default build, `cargo nextest run`, and the REPL stay Cranelift-only and LLVM-free (feature-gated — §5).

### 1.2 Non-goals
- **NG1 — Not the dev/REPL backend.** LLVM compile latency (whole-module IR + `opt`/`llc` + LTO) is seconds-to-minutes; the REPL and `--run` stay Cranelift forever.
- **NG2 — No new language features.** Display protocol (0050), `/learn` (0052), `Type.member` (0365) are *other* Phase-H items.
- **NG3 — No semantics-driving representation change in the MVP.** The S83 §12.1 per-type-representation relaxation MAY be exploited later (Perceus in-place reuse, §8); the MVP keeps the identical heap/ABI layout (§4).
- **NG4 — Not a JIT, and no tracing GC** (§8 — GC breaks determinism/FFI/concurrency).

---

## §2. The two-tier framing (the organizing idea)

The old framing — "`--release` adds an LLVM backend" — put the codegen engine at the center. That is wrong by altitude. **Two tiers, one facade:**

| Tier | Trigger | Codegen | Memory model | Calls | Optimization | Purpose |
|---|---|---|---|---|---|---|
| **Dev / correctness** | `--run`, `--link`, REPL | Cranelift | Uniform atomic RC, per-node drop glue | GOT-indirect (JIT-patchable) | none — *simple, identical lowering* | Fast compile; incremental; the correctness oracle |
| **Efficiency** | `--release` | **LLVM** (component) | M3–M7 (§6/§8) | M1 direct + inline | M1–M7, all of it | Final runtime space + time |

The release tier is the set **{M-LLVM, M1…M7}** (§6). LLVM codegen is *one* of those — it produces machine code after the efficiency mechanisms have rewritten the program; it brings LTO (M2) and inline RC-fusion (M3) "for free" as IR passes.

**The split is principled.** Cranelift stays the simple correctness tier *precisely because* it carries no optimization. Every `--run`/REPL invariant — JIT memory reclaim (Decision 31, `Arc<Jit>` + `free_memory()`), per-symbol GOT patching (Decision 41), REPL redefinition immediacy — depends on GOT indirection being load-bearing. The efficiency tier elides exactly that indirection (it is **closed-world**: single static exe, `-force_load`'d platform rlibs, no `dlopen`), so it *must* be a separate lowering path. The two tiers share **one input: the unchanged `MonoExpr`/`MonoDefn` facade** (`crates/cranelisp-types/src/mono_expr.rs`), and prove equivalence by **semantic differential testing** (§11).

**Consequence:** the entire efficiency tier lives downstream of the `MonoExpr` boundary. Nothing about the program's *meaning* changes between tiers — only the lowering of that meaning to machine code + memory operations. That is the property that makes backend-encapsulation viable (§7).

---

## §3. The codegen boundary — a second `MonoExpr` consumer

The load-bearing fork: *from what artifact does the release tier lower?*

- **(a) Cranelift IR → LLVM IR.** Rejected — CLIF is a *lowered* IR that has already discarded the typed structure (`ConcreteType`, ADT tags, RC intent) LLVM's optimizer wants to *see*; it also couples us to two version-locked toolchains forever.
- **(b) A parallel lowering of the same post-mono `MonoExpr`.** **Recommended.**
- **(c) Emit C, compile with clang.** Rejected as the product path (a third textual ABI surface to keep locked; weaker control of the consuming convention + atomic RC + tail calls). Retained only as a possible early de-risking spike.

**Recommendation (b).** The S84 full-monomorphisation arc built `MonoExpr`/`MonoDefn`/`MonoDefnVariant` (`crates/cranelisp-types/src/mono_expr.rs`): a post-mono codegen AST where every node carries a non-optional `ty: ConcreteType` (`concrete.rs` — no `Var`, no `TyConApp`) and every call carries `resolved_call: Option<Box<ResolvedCall>>` (mono_expr.rs:124) naming a concrete target (`TraitMethod{mangled_name}`, `SigDispatch`, `BuiltinFn`, `AutoCurry`). **Trait dispatch is already statically resolved — there is no vtable.** This is exactly the artifact a second backend should consume. Everything above it — reader, macro expansion, Algorithm-W, trait resolution, monomorphisation — is reused verbatim. The LLVM backend is a function `MonoDefn → LLVM IR`, mirroring the Cranelift `FnCompiler::compile_expr` dispatch, one method per `MonoExpr` variant.

**Single source of truth for codegen input (Principle 7):** the release tier consumes the *same* `MonoExpr` instances Cranelift would — never a re-derived or release-specific IR. If `--release` ever needs information `MonoExpr` doesn't carry, that information is added to `MonoExpr` (benefiting both tiers) — the S100 ownership-inference fields (`design/arch/ownership-inference.md` §3.3) are exactly this rule operating: one contingent case fired (§8.3), the facts joined the shared boundary, and both tiers consume them.

---

## §4. ABI / runtime / platform compatibility — the hard constraint

A second lowering path silently kills you here. **DEF-6 (S86)** is the cautionary tale: `HostCallbacks::alloc` must return a *payload* pointer (base + `HEAP_HEADER_SIZE`); the `--link` path had wired `heap_alloc` (base) where the JIT path used `heap_alloc_payload` — every host↔DLL crossing stored 16 bytes too low, clobbering the RC header, and glibc reported "double free" only after ~40 crossings (`crates/cranelisp-exe-bundle/src/lib.rs:131-144`; Risk 11, `tests/plan/risks.md` — "invisible below a threshold and catastrophic above it"). A one-offset JIT-vs-link divergence cost a sprint. A third lowering triples that surface.

**Governing principle:** the release tier's *MVP* introduces ZERO new ABI facts — it re-emits, in LLVM IR, byte-identical lowerings of the same contracts. It must honor:

- **§4.1 Heap layout (representation containment).** 16-byte header; base-pointer convention; positive-offset fields; no interior pointers. All layout constants (`HEAP_HEADER_SIZE`, ADT `TAG_OFFSET`/`FIELDS_START`, closure `CODE_PTR`/`DROP_GLUE`/`CAPTURES` offsets, Vec `LEN/CAP/DATA_PTR`) are the **single source of truth and MUST be shared, not re-typed** — imported from `cranelisp-backend::heap` (or promoted to a shared leaf). Only the LLVM analogue of `heap_load`/`heap_store`/`emit_*_alloc` touches offsets; no raw byte offsets anywhere else.
- **§4.2 Consuming convention + RC contract.** Callee owns heap params; caller emits inc for non-last-use, transfers on last-use (Decision 24; `src/CLAUDE.md §Scope Management`). RC ops are atomic (NFR C.4.1: `fetch_add(1, Release)`; `fetch_sub(1, Release)` + `fence(Acquire)` before free — `cranelisp-intrinsics/src/rc.rs`; emitted inline in `heap.rs:173/236`). **MVP: the release tier reproduces the same inc/dec placement** Cranelift produces (driven by `compute_last_uses`, `heap.rs:912`, consumed at `control_flow.rs:465`). Non-atomic/fused/elided RC is an *optimization* (M3/M4), gated behind parity (§8/§11).
- **§4.3 GOT / platform ABI.** Per-module GOT data symbol (`got_data_symbol_name`), platform GOT `__cranelisp_got_platform_<name>`, manifest `cranelisp_platform_manifest_<name>`, layout-hash `__cranelisp_layout_hash_<name>` (`platform-interface.md §1`). **MVP emits byte-identical relocation names** so the existing linker drivers resolve them. The layout-hash gate (refuse on mismatch) is emitted in the startup stub. *(M1 later elides the GOT in release — §6 — but the MVP keeps it for parity-by-construction.)*
- **§4.4 Runtime intrinsics + exe-bundle wiring.** All emitted calls (`alloc`, `drop`, `io`, `ivar`, `panic`, `rc`, `trace`, vec/string-internal) resolve to the **same** `cranelisp-intrinsics` symbols force-linked into `libcranelisp_exe_bundle.a`. The startup contract — `cranelisp_init_primitives()` + `cranelisp_init_platform(manifest_ptr)` with **`alloc: heap_alloc_payload`** (the DEF-6 contract) — is identical. **MVP calls intrinsics, does not inline them** (§8.1): LLVM and Cranelift then exercise the same machine code at the dangerous seams; LTO inlines them later, parity-gated.

**How parity is guaranteed, not hoped** (in strength order): (1) **share, don't mirror** the layout consts + GOT-naming; (2) **call intrinsics, don't inline** in the MVP; (3) **differential + sustained-load testing** (§11) — the DEF-6/Risk-11 class.

---

## §5. Crate structure — a feature-gated submodule of `cranelisp-backend`

**Decision (revised per the encapsulation steer): the entire efficiency tier is a feature-gated submodule `cranelisp-backend/src/release/`, NOT a separate crate.**

```toml
# crates/cranelisp-backend/Cargo.toml
[dependencies]
inkwell = { version = "...", optional = true }   # not compiled unless enabled
[features]
release = ["dep:inkwell"]                          # OFF by default
```
```rust
// crates/cranelisp-backend/src/lib.rs
#[cfg(feature = "release")]
pub mod release;   // M1..M7 + M-LLVM — the whole efficiency tier
```

**Does an off-by-default feature keep LLVM out of `cargo build` / `cargo nextest run`? Yes, with one discipline.** The workspace is `resolver = "2"` (root `Cargo.toml`); feature unification is per-build-graph and triggered by *whoever enables the feature*. So:
1. `release` is in no crate's `default`; a plain build/nextest never enables it → `inkwell` (optional dep) is never compiled. The dev build and the ~9s suite stay LLVM-free. ✔
2. **Discipline: no crate may list `release` in `default`, and no `dev-dependency` may enable it.** Release codegen is reached only via explicit `cargo build -p cranelisp --features release`. ✔
3. Tests *of* the release tier sit behind `#[cfg(feature="release")]` and run in a separate `cargo nextest run --features release` lane — they don't pollute the default suite's compile graph or its time budget.

**Toolchain:** `inkwell` (safe LLVM-C wrapper) pinned to one LLVM major (propose **LLVM 18**), discovered via `LLVM_SYS_180_PREFIX`/`llvm-config`. `llvm-sys` (raw) rejected; textual-`.ll`-shell-out kept only as a spike. **Users:** the published release binary is built *with* `release` so end users get `--release` without installing LLVM (resolved at *our* build time; the produced exe has no LLVM runtime dep). **CI:** one extra LLVM lane builds + runs the `release`-gated parity/perf suites; the main lane stays LLVM-free.

**Why submodule beats a split crate here:** the residual reasons for a crate (compile blast-radius, `build.rs` provisioning, dependency-graph legibility) are all *avoidable* with strict feature-gating and don't outweigh the user's encapsulation goal. Revisit only if system-LLVM `build.rs` provisioning genuinely entangles the default build (it should not).

**What is shared lives where it already is.** Layout constants and `got_data_symbol_name` should be single-sourced (note: `got_data_symbol_name` currently has a byte-identical duplicate — `cranelisp-types/src/module.rs` claimed-canonical vs. `cranelisp-backend/src/compiler/mod.rs` `pub(crate)` copy the backend actually calls — a latent Principle-7 drift to fold when release lowering touches call emission). The RC-decision analyses (`compute_last_uses`, `HeapCategory::classify`) **stay in the backend** (see §7/§9) — `classify` was deliberately relocated *into* the backend (S69 Sub 38, "zero consumers outside this crate"); the release passes extend it in place.

---

## §6. The efficiency mechanisms (closed-world)

Every mechanism is unlocked by the closed-world property (§2): a `--release` binary is a single statically-linked exe (user objects + `libcranelisp_exe_bundle.a` + `-force_load`'d platform rlibs), no `dlopen` anywhere (confirmed: `platform-interface.md §1` "no dlopen exists anywhere in a linked program"; dynamic loading is confined to `src/platform.rs`'s live-session cdylib path), no incremental JIT/REPL patching. Every call target, every linked platform, every symbol is fixed at compile time.

- **M-LLVM — LLVM codegen.** Lowers `MonoExpr → .o` (§3). The engine, not the organizing idea.
- **M1 — GOT-elision / direct calls + inlining.** The per-module GOT (`got_data_symbol_name`, dispatched via `emit_got_indirect_call_via_data_id`) is a runtime-mutable `AtomicPtr` slab whose *only* load-bearing purposes are incremental-model concerns: JIT per-symbol patching (`got.rs:131-152`), `.o`-cache relink, REPL hot-reload, and **cdylib** platform dispatch. In `--link`/`--release` the platform rlib is `-force_load`'d and slots are resolved at `ld` time as ordinary linker symbols — the indirection is structural uniformity, not necessity. **In release, lower `resolved_call` to a direct `call @sym`** (platform effects included — they're static rlibs, so even effect calls are directly callable/inlinable). Because dispatch is already monomorphised, "inlining across calls" is just emitting a direct edge to a known body and letting LLVM inline. *(Note: the tempting "keep GOTs, let LTO devirtualize through them" route does **not** work — the optimizer can't prove a mutable atomic global has one value; you'd have to emit it as a constant, which is just an awkward direct call. So emit direct refs.)*
- **M2 — Whole-program optimization (ThinLTO).** LTO spanning user objects + bundle `.a` + platform rlibs unlocks cross-module inlining, whole-program DCE (strip unused prelude/stdlib/runtime), and const-prop — and it is the **enabler** for M1's inlining and M3's RC-fusion (the optimizer can't fuse what it can't see across a native-object boundary). **Intrinsically Tier-2-only:** a Cranelift `.o` cannot join an LLVM LTO unit. ThinLTO default; fat-LTO opt-in for small programs.
- **M3 — RC inc/dec fusion (peephole).** Once M2 inlines the RC intrinsics, `inc(x); dec(x)` cancellation and loop-hoisting become LLVM-IR/LTO passes. Safe freebie.
- **M4 — Non-atomic RC (confinement-gated).** The atomics exist for two structured fork-join paths: lenient-eval IVar sparks (`ivar.rs`) and S85 auto-IO `ParBranch` (`io.rs`). Both boundaries are **visible on the facade** (`MonoExpr::ParBind`, mono_expr.rs:146). Allocations that never cross a spark/`ParBind`/IVar boundary are thread-local and get *plain* add/sub (`emit_rc_inc_local` vs the atomic `emit_rc_inc`). Soundness-critical (conservative — atomic on any doubt); the heaviest differential coverage applies. *(S100: the confinement fact is the typecheck-computed Q3 advisory — spine §2.3 — interprocedural, not a backend-local walk; the emission mechanism stays here and lands on the shared lowering.)*
- **M5 — Escape analysis → stack/region alloc.** An allocation whose result never escapes its defining function is stack/region-allocated instead of `emit_alloc`, eliminating the alloc *and* its RC pair. *(S100: the escape fact is the typecheck-computed Q2 advisory — spine §2.2, with suspension crossings as escape edges — superseding the earlier "direct extension of `compute_last_uses`" framing; the intra-function `compute_last_uses` walk stays in-backend for last-use, and the stack/region mechanism stays here, landing on the shared lowering.)*
- **M6 — Perceus precise-RC + in-place reuse.** Drop-guided reuse: a unique (`rc==1`) constructor consumed at last use, followed by a same-layout construction, reuses the memory in place. **This is the principled fix for FIXME 0408**: a uniquely-owned Sudoku grid's `set-cell` becomes an in-place store instead of an 81-cell copy, collapsing quadratic copy-per-guess to constant. Connects to the S83 §12.1 representation freedom. *(S100: the borrow/own knowledge arrives from typecheck via the ownership-inference contract, and reuse lands on the shared lowering ahead of `--release` — see §8.3 ruling box + `design/arch/ownership-inference.md` §4.3/§7.)*
- **M7 — Arena/region per lifetime.** The aggregate of M5 escape results — group allocations of common bounded lifetime (a `let` body, a `ParBind` arm) into one arena freed at scope exit. A natural fit for per-request lifetimes (the web exemplar). Region boundaries are structurally visible (`Let`, `Match` arms, `ParBind` arms).

**No tracing GC** — it breaks deterministic destruction (the consuming convention assumes eager ordered finalization), the C-ABI/platform model + DEF-6 alloc contract (a moving collector invalidates pointers held across FFI), and the atomic-RC concurrency story. Perceus + escape/region gives most of GC's allocation-elision while *preserving* determinism, the FFI contract, and concurrency.

---

## §7. Encapsulation & facade-impact map (core deliverable)

Question per mechanism: **can it be a release-only pass inside `cranelisp-backend/src/release/` consuming the UNCHANGED `MonoExpr`, or does it need something the facade above (typecheck → `MonoExpr`) doesn't provide?**

The decisive precedent: the two analyses beyond-RC needs **already live in the backend and already run purely off `MonoExpr`/`ConcreteType`** — `compute_last_uses` (heap.rs:912, a `MonoExpr` walk) and `HeapCategory::classify` (heap.rs:438, total over the six `ConcreteType` variants). So uniqueness/escape/region has everything it needs *already inside the backend*.

| M | Mechanism | Classification | Facade delta |
|---|---|---|---|
| M1 | direct calls + inline | **ENCAPSULATED** | none — `resolved_call` already names the static callee; direct-call is a release lowering mode |
| M2 | ThinLTO / WPO | **ENCAPSULATED (codegen) but BUILD-SYSTEM-impacting** | none on the facade; needs `[profile.release] lto` + bitcode-emitting platform/bundle rlibs (workspace `Cargo.toml` + platform crates) — the one non-facade exception |
| M3 | RC fusion | **ENCAPSULATED** | none — post-lowering LLVM-IR/LTO peephole |
| M4 | non-atomic RC | **mechanism ENCAPSULATED; precision fact CONSUMED from the facade** *(S100)* | consumes the typecheck-computed **confinement** advisory fact (ownership-inference spine §2.3/Q3); sound to ignore. Lands on the **shared** Cranelift lowering per the §8.3 ruling, no longer release-only. |
| M5 | escape → stack/region | **mechanism ENCAPSULATED; precision fact CONSUMED from the facade** *(S100)* | consumes the typecheck-computed **escape** advisory fact (spine §2.2/Q2); `compute_last_uses` stays in-backend. Lands on the shared lowering. |
| M6 | Perceus reuse | **mechanism ENCAPSULATED; contract facts CONSUMED from the facade** *(S100 — the §8.3 contingency FIRED)* | consumes the **ABI-bearing per-param mode vector** + advisory uniqueness facts (spine §3); dynamic rc==1 reuse tokens stay intra-function, off the call ABI (spine §3.5). Lands on the shared lowering. |
| M7 | arena/region | **ENCAPSULATED** | none — region boundaries (`Let`/`Match`/`ParBind`) are first-class facade nodes; aggregation of M5 results, which now arrive via the spine's escape facts |

**Summary (amended S100): the codegen-engine mechanisms (M-LLVM, M1–M3, M7-aggregation) encapsulate with zero facade delta; the memory-model mechanisms (M4–M6) keep their *mechanisms* backend-encapsulated but consume interprocedural *facts* computed at typecheck and carried on the `MonoExpr`/signature boundary** — the S100 ownership-inference contract (`design/arch/ownership-inference.md` §3). The lone non-codegen exception remains **M2 (build-system, not facade)**. D-Rel-5's "`MonoExpr` frozen" is superseded for the ownership-inference fields (§8.3 ruling box); the line is now: **interprocedural facts above the boundary; intraprocedural analyses and all mechanisms below it.**

---

## §8. Memory management beyond RC — two layers

**Layer 1 — RC peephole (LTO-reachable):** M3 fusion is a safe freebie once M2 inlines the intrinsics. M4 non-atomic RC is **not** a freebie — it needs the confinement fact (S100: typecheck-computed, spine §2.3; consumed by the backend emission per §6) and is where over-optimization = use-after-free across a join.

**Layer 2 — RC replacement/augmentation (compiler analyses over `MonoExpr`, NOT LLVM freebies):** M5 escape, M6 Perceus, M7 region. These cut allocation/RC-op *count* (algorithmic) — categorically distinct from LLVM's constant-factor wins.

### 8.1 The MVP discipline vs. the optimizations
The MVP proves **identical lowering** (parity by construction): same GOT-indirect calls, same intrinsic calls (not inlined), same RC schedule as Cranelift — differing only in the IR target. Each of M1–M7 is then an **opt-in release-only switch** layered on *after* MVP parity holds. They never touch `--run`/`--link` lowering.

### 8.2 Parity shifts from byte-identity to semantics
Once release lowering legitimately diverges, the invariant becomes **same observable output across `--run`/`--link`/`--release`** for the whole corpus (§11). Differential testing replaces byte-identity as the oracle.

### 8.3 The M6 watch-item (the one standing facade exception)

> **S100 RULING (2026-07-02, `/arch` Phase-2 review — the contingency below has FIRED; the default is INVERTED).**
> The S99 measured settlement (`effect-concurrency.md` §3.1; `ring2-rc.md` §5.5.2.7) established that the
> dominant contention term (vec-COW leaf-refcount volume) is curable only with interprocedural facts local
> in-backend derivation cannot see — exactly the "can't reach the precision FIXME 0408 needs" condition this
> section named. S100 rules: **ownership/mode inference is computed at typecheck (interprocedural, over the
> resolved call graph, no annotations) and passed down on the `MonoExpr`/signature boundary.** Per-param
> signature modes are ABI-bearing (absence ⇒ the Decision-24 Owned/consume default); per-site
> escape/confinement/uniqueness facts are advisory (sound to ignore). Intraprocedural analyses
> (`compute_last_uses`, `HeapCategory::classify`) and all codegen *mechanisms* stay backend-encapsulated;
> the mechanisms additionally land in the shared Cranelift lowering (partially superseding D-Rel-4's
> "dev path stays unoptimized" for the memory-model subset — the conservative all-Owned lowering remains
> the correctness oracle). D-Rel-5's "`MonoExpr` frozen" is superseded for these fields. Full contract:
> the S100 Phase-3 arch spine **`design/arch/ownership-inference.md`** (landed 2026-07-02 — the
> lattice §2, the two-class contract §3, sequencing §4, the R3 dependent-recompilation model §5,
> soundness discipline §6); the §7 table and §13 have been amended in step with it.
> Recorded in `sprints/SPRINT.md` §Architecture review (S100).

Perceus precision improves with borrow-vs-own knowledge. The calling convention is **uniformly consuming** (Decision 24 — the backend has no borrowing classification). **Recommendation: derive borrow/own in-backend** from `MonoExpr` use-structure (a parameter used only in non-escaping read positions is borrowable) rather than adding a facade field — preserving encapsulation at some precision cost. *Only if* in-backend derivation can't reach the precision FIXME 0408 needs does a typecheck-side ownership annotation on `MonoExpr` become warranted — and that piece would necessarily live above the backend. This is the single contingent breach of the encapsulation goal.

---

## §9. Linking and the executable — reuse the entire `--link` tail

The release tier's codegen ends at emitting `.o`s; **everything downstream is the proven path.**
- LLVM emits one `.o` per module (object, or bitcode `.o` under LTO) — slotting where Cranelift's `compile_to_object` `.o`s go.
- **Startup stub stays Cranelift-emitted in the MVP** (`src/exe.rs` `generate_startup_object`/`generate_main_alias_object`) — tiny, ABI-critical (DEF-6 lives here), not perf-relevant. One fewer thing to re-verify.
- **Linking is the existing `link_executable`/`LinkRequest`/`Linker` trait** (`src/exe.rs`, `src/link/{gnu,apple}.rs`). LLVM `.o`s are ordinary ELF/Mach-O; the drivers link them unchanged, preserving the standalone-stripped-exe contract (~2.76 MiB today). **Do not drive `lld` separately** — the abstraction already handles rlib `-force_load`, the bundle `.a`, and stripping. (Enabling `--gc-sections`, currently a deliberate no-op in `src/link/gnu.rs`, is part of the M2 build-config.)
- Static runtime + platform handling identical to `--link`. For LTO, the bundle `.a` + platform rlibs must ship bitcode (M2 build-config).

**Net:** `--release` = (efficiency-tier-lowered, LLVM-optimized `.o`s) + (the entire existing `--link` orchestration, unchanged).

---

## §10. CLI / pipeline integration (`/int` handoff)

`--release` is a new mode parallel to `--run`/`--link`; routing lives in `src/main.rs`/`src/exe.rs` (the `/int` bounded context). It (a) compiles with the `release` feature, (b) drives `[profile.release] lto`, (c) does the closed-world link. Behind `#[cfg(feature="release")]` with a clean error when the feature is off. Mode-exclusivity (`--release` + `--run`?), `--no-cache` honoring, and **release-artifact cache namespacing** (extend the cache key with `(backend, opt_level)` so a debug `.o` is never confused for a release `.o`) are `/int` + `/backend` work. The `repl/spec.md §0.6` flag-table addition is **/repl-owned** → a FIXME to file when Phase H is scoped (not now — the design is unratified).

---

## §11. Verification strategy (`/qa` handoff)

**The acceptance gate: byte-identical observable output across `--run`, `--link`, and `--release`** — the DEF-6 divergence class, re-opened by a third lowering.
- **Three-mode differential harness** over the existing free-standing `examples/`+`tests/` corpus, gated behind the `release` feature. MVP corpus is a risk-ramp: Int/Bool arithmetic → String (heap+RC) → ADT+match (tags+drop glue) → closures → Vec → a platform program (GOT+manifest+layout-hash+DEF-6 alloc-payload crossing) → `trace` → `ParBind`/auto-IO.
- **Sustained-load + checking-allocator** (the Risk-11 guard output-equality unit tests miss): a release-built program doing thousands of crossings/allocations/RC cycles, asserting no corruption + balanced RC. M4 (non-atomic RC) and M6 (in-place reuse) need the heaviest concurrent + aliasing coverage.
- **Performance benchmark harness:** Sudoku (~3.3 s baseline) measured under `--release` before/after the 0408 rework (to attribute codegen vs. algorithm wins cleanly), plus a numeric loop, an alloc-heavy loop, and a parallel map-reduce. Honest per-G2 reporting.

---

## §12. Phased delivery

- **H.0 — Pre-reqs.** Single-source the layout consts + fold the `got_data_symbol_name` duplicate (§5). (Note: this is *lighter* than the original design's "extract RC analysis above backend" — that is reversed; the *intraprocedural* analyses stay in-backend per §7. S100: the *interprocedural* facts arrive from typecheck per the ownership-inference spine — a different, designed split, not the extraction this note declined.)
- **H.1 — MVP.** `cranelisp-backend/src/release/` behind `release`; lower `MonoExpr → .o` via inkwell at `-O2`, **calling all intrinsics (no inlining)**, GOT-indirect (parity-by-construction); reuse startup stub + linker tail; `--release` CLI. **Acceptance: three-mode byte-parity on Int→ADT→closure→Vec + one platform program + the sustained-load test.** No perf claim — correctness first.
- **H.2 — Optimize.** M2 ThinLTO (substrate, first) → M1 direct calls → M3 RC fusion → M5 escape → M6 Perceus (parity-gated, ASan-checked) → M4 non-atomic RC (confinement-gated, last/hardest) → M7 region. `-O3` per-benchmark. **Acceptance: measured speedups.**
- **H.3 — Exemplar perf numbers.** `--release` Sudoku, before/after the 0408 rework — the headline showcase number.
- **Gating:** Phase H is GATED (ROADMAP row H). This design is an input to that gate.

---

## §13. Decisions record

- **D-Rel-1 — Two-tier framing.** `--release` is the efficiency tier; LLVM is one component (M-LLVM); Cranelift stays the simple dev/correctness tier. (§2)
- **D-Rel-2 — Second `MonoExpr` consumer** (option b), not CLIF→LLVM or emit-C. (§3)
- **D-Rel-3 — Feature-gated submodule** `cranelisp-backend/src/release/`, not a split crate; `release` off by default; LLVM stays out of the dev build/9s suite. (§5)
- **D-Rel-4 — Encapsulation over sharing.** Efficiency analyses (M1–M7) are release-only and backend-encapsulated; they are **NOT** extracted above the backend to benefit both tiers (this *inverts* the closed-world addendum's earlier recommendation). Consequence (accepted): the Cranelift dev path stays unoptimized — intended; it's the correctness oracle, not the efficiency path. (§7, §8) *[**AMENDED S100** (Phase-3, `design/arch/ownership-inference.md`): superseded for the memory-model subset — ownership/escape/confinement/uniqueness **facts** are computed at typecheck and carried on the boundary (the spine's two-class contract §3), and the M4–M6 **mechanisms** land in the **shared Cranelift lowering** (spine §3.4), no longer release-only. The correctness-oracle role is preserved by the analysis-off toggle (conservative all-Owned/atomic/heap lowering, spine §6.2). Intraprocedural analyses (`compute_last_uses`, `HeapCategory::classify`) and all mechanism internals stay backend-encapsulated. Codegen-engine mechanisms (M-LLVM, M1–M3) unaffected — still release-tier-only. See the §8.3 ruling box.]*
- **D-Rel-5 — `MonoExpr` facade frozen w.r.t. the efficiency tier**, with one contingent exception: M6 Perceus borrow-precision, declined in favor of in-backend derivation unless FIXME 0408 demands otherwise. (§7, §8.3) *[**AMENDED S100**: the contingent exception FIRED (S99 measurement — in-backend derivation cannot see the interprocedural facts the dominant vec-COW term needs); the freeze is superseded for the ownership-inference fields (`ModeSummary` on `MonoDefnVariant` + advisory site facts on `MonoExpr` — designed in the spine §3.3, landed by the first implementation sprint, `/arch`-authored). The freeze STANDS for everything else; every further field is judged against the spine's narrowness counterweight (Principle 2 — the boundary carries only what locality cannot compute). See the §8.3 ruling box.]*
- **D-Rel-6 — MVP proves identical lowering; optimizations layer on; parity then = semantic differential testing under sustained load.** (§4, §8.1–8.2, §11)
- **D-Rel-7 — No tracing GC.** (§6, §8)

---

## §14. Risks

| Risk | Mitigation |
|---|---|
| **LLVM-as-dependency** (build weight, version drift, packaging) | Feature-gated off by default (§5); dev loop never touches it; pin LLVM 18; isolated CI lane. |
| **Second-lowering maintenance** (two paths must stay equivalent) | Share-don't-mirror the layout consts + GOT-naming; differential + sustained-load tests as standing guards. The *dominant* long-term risk. |
| **Silent ABI divergence (DEF-6 class)** | MVP calls intrinsics (no inline), GOT-indirect, identical relocations; reuse the identical startup stub + linker tail; three-mode + sustained-load tests. |
| **RC atomics mis-modeled** (M4 over-elimination → use-after-free) | M4 confinement-gated, deferred, conservative; ASan-checked; correct fence modeling. |
| **M2 build-config drift** (bitcode rlibs) | Explicit `[profile.release]` + platform-crate build settings; the one non-facade exception, owned by /platform + /int. |

---

## §15. Open questions / user sign-off

Before implementation (none block current work — Phase H is gated):
- **U1 — D-Rel-2** (the `MonoExpr`-consumer boundary). Confirm.
- **U2 — D-Rel-3** (feature-gated submodule + inkwell/LLVM 18, off by default). Confirm.
- **U3 — D-Rel-4** (encapsulation over sharing; Cranelift dev path stays unoptimized). Confirm — this is the consequential inversion. *(S100: partially superseded for the memory-model subset — see the amended §13 entry; what remains to confirm is the codegen-engine half.)*
- **U4 — H.0 timing.** The (now-light) pre-req consts/dedup work: in the first release sprint, or pulled into the S87 audit-remediation?

---

## Cross-skill handoffs / Next skills

*(To be filed as `design/arch/fixmes/NNNN-*.md` when Phase H is scoped — not now; the design is unratified.)*
- **`/backend`** — owns the whole efficiency tier: `src/release/` (M1–M7 + M-LLVM), the H.0 const-single-sourcing + `got_data_symbol_name` dedup, and the ABI-parity review. *(S100 amendment: the M4–M6 memory-model mechanisms are designed and landed on the **shared** lowering ahead of `--release`, consuming the ownership-inference facts — `design/backend/ownership-codegen.md` against the spine; `--release` inherits them.)*
- **`/platform`** — M2 exception: platform rlibs + `cranelisp-exe-bundle` emit LLVM bitcode under release so ThinLTO sees across the FFI boundary.
- **`/int`** — `--release` CLI routing, mode-exclusivity, `[profile.release] lto`, release-artifact cache namespacing (§10).
- **`/typecheck`** — *(S100: the standing contingency FIRED — S99 measured exactly the precision ceiling this bullet reserved against.)* Typecheck owns the **interprocedural ownership/escape/confinement/uniqueness inference** (computed post-mono over the resolved call graph) whose outputs ride `MonoDefn`/`MonoExpr` per the S100 contract — see `design/arch/ownership-inference.md` (spine) and `design/typecheck/ownership-inference.md` (the per-crate proposal).
- **`/qa`** — the three-mode differential + sustained-load/checking-allocator harness + the benchmark harness (§11). The sustained-load test is the DEF-6/Risk-11 guard and is not optional.
- **`/port`** — the Sudoku `--release` measurement (§11, H.3), composed with the FIXME-0408 rework.
- **`/repl`** — the `repl/spec.md §0.6` `--release` flag-table addition (file when scoped).
- **`/spec`** — no MVP change (G3). The S83 §12.1 per-type-representation relaxation is a future M6 opportunity (NG3), flag only if H.2+ exploits it.
