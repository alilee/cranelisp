# JIT / object codegen convergence

> **Owner**: `design` (backend). **Status**: §1 is a standing contract, graded
> *asserted-with-a-named-falsifier* — §1.3 names the falsifier, and no executing
> check compares the two finalize paths against each other (§2).
>
> Source and tests cite this document by path and section (`src/scheduler.rs`
> cites §1; `tests/regression.rs` cites §1.1). Check those before renumbering.

## §1 Invariant statement

Decision 23's two-GOT model, Decision 36's bare-Local naming, Decision 37's
one-recursive-flow cache-hit integration and Decision 35's per-entry `Code`
retention together imply a formal invariant:

> **JIT-object convergence invariant.** For any module `M`, the sequence of
> steps carrying `M`'s source to reachable executable bytes is identical across
> the JIT finalize path and the `.o` relocation + link-load path, **except for a
> single explicitly-bounded fixup-mechanism boundary**. Bytes upstream of the
> boundary are bitwise-identical; bytes downstream carry the same semantics — a
> function pointer that, when called, executes the same instructions against the
> same GOT slots — produced by a different mechanism.

A breach is a correctness bug in its own right, independent of any symptom it
happens to produce. It is not "only a caching concern".

### 1.1 What MUST be identical

| Artifact | Rationale |
|---|---|
| **CLIF emitted by `compile_to_module<M: Module>`** | It is the sole emission entry and does not branch on `M` for any decision affecting emitted instructions. The same inputs must give byte-identical CLIF for the JIT's module (§3) and `ObjectModule`. |
| **Function symbol names** | Every user defn is declared bare-name with `Linkage::Local` in both paths (Decision 36). No per-mode mangling. |
| **GOT slot layout** — which symbol occupies which per-module slot index | Pinned before any codegen runs, persisted to cache, re-installed unchanged on cache-hit (Decision 37 order-independence). |
| **Callee resolution shape** — calls to redefinable language functions read their code pointer from `__cranelisp_got_{M}` slot `i` | Decision 36 "why all-GOT calling" plus the Decision 31 safety invariant. A direct relocation against a function symbol would break REPL redefinition and is forbidden. |
| **RC conventions** — which parameters are consumed, where inc/dec emit | The consuming convention is a property of the CLIF, not of the fixup mechanism (`ring2-rc.md`). |

**Drop glue is compilation-local and has no GOT slot.** `design/arch/bounded-contexts.md` §3 ("Result-owner
access to named type glue") rules that glue has no GOT slot — it is neither
language-callable nor redefinable, and all-GOT calling exists for late binding
of symbols that are both. Glue is emitted and referenced as ordinary CLIF in
the same `compile_to_module` transaction as its callers, so rows 1 and 5 already
cover it. The closure word that stores a glue address is the published layout of
BC §4b invariant 5, and that address's retention owner is the entry `Code`
(Principle 22) — not this document's concern.

### 1.2 What MAY differ — the single fixup-mechanism boundary

| Downstream step | JIT path | Object path |
|---|---|---|
| Resolve the `__cranelisp_got_{M}` data symbol | `JITBuilder`'s symbol lookup returns the module's live `got().base_ptr()` at finalize | Under `--link`, the system linker reads the `.o`'s exported GOT data symbol, initialised with relocations against the local function symbols. On a JIT cache-hit the in-process `cache::Linker` resolves it from the externally registered `SymbolTable` GOT base, which is the sole authoritative resolver — the `.o`'s own GOT data symbol must not shadow it |
| Make function pages executable | `finalize_definitions()` through `CodeFinalizer` | No-op at compile time; relocation + mmap at load time |
| Produce the per-symbol entry address | Read from the finalized function after finalize | Unavailable at compile time; resolved later on cache-hit through `Linker::get_symbol(bare_name)` |
| Retention root | `Code::Jit(Arc<Jit>)` | `Code::Linker(Arc<Linker>)` |
| Reclamation primitive | `Jit::Drop` frees the JIT's executable memory at refcount 0 | `Linker::Drop` reclaims the mmap'd pages at refcount 0 |
| Reach a compilation-local callee | Every call is compiled far: an absolute address and an indirect branch (§3) | A pc-relative call within the object's one text section |

The last two rows name *what* reclaims an owner, not *when*: staged and compiled
publication in a live session move displaced `Code` into the session-lifetime
retention pool (`design/int/session-transaction.md` §6–§7, under
Principle 22). Both mechanisms run when that owner is finally released.

**That table is exhaustive.** Every other step — read, expand, typecheck,
annotation, registration, GOT-slot allocation, CLIF emission including RC ops
and drop-glue references, and the object-mode GOT data emission — runs
identically on both paths.

### 1.3 How the invariant is falsified

**CLIF diff.** Emit `M`'s targets under both `Module` types from identical typed
state and byte-compare per function. Any divergence is a breach.
`CRANELISP_CODEGEN_DUMP` supplies the dumps.

**One known breach, semantics-preserving.** A trace form's CLIF follows
hash-map iteration within each covered module, so two compilations of one
module can order its wrappers, descriptors and swapped slots differently. Each
compilation is self-consistent, so the trace records the same calls. The
correction is [trace codegen](trace-codegen.md) §1.3 (open). It is the reason
the rule is stated as a function of the inputs
([backend](backend.md) §6), not as a property of one compilation.

Slot *contents* are not a second falsification. A fresh JIT finalize and a
`Linker` mmap are independent loads into different pages; equal addresses across
them are neither expected nor informative, and inequality is not a breach. The
per-load property that does matter is already structural: on a cache-hit the
slot is written from that load's own `Linker::get_symbol` result, with a located
hard error when the symbol is missing, and on a fresh build from the same
finalize that produced the address.

## §2 Evidence obligation

The invariant has **no executing guard**. §1.3's falsification is asserted, not
measured — the grade is *asserted-with-a-named-falsifier*. Partial substitutes
exist (`clif_dump_tests.rs`, the golden-CLIF lanes, `module_assembly_tests.rs`,
the link/run parity e2e), but none compares the two finalize paths against each
other.

Two guards would discharge it. Allocation is `qa`'s and has not been made; this
document states the questions, not a test plan:

1. the same source produces the same CLIF under both `Module` types;
2. a fresh build fails loudly if any defined symbol's slot is unpopulated — the
   cache-hit leg of the same question is already a structural hard error.

## §3 Call reach in the JIT (ACT-1070)

**Status:** built at `790f4c9a` (S124 row B13; `arch` approved the public
delta on 2026-11-19 with the wrapper crate-private). Verified against
`jit.rs` at `81d186c6`.

**Fault.** `cranelift-jit` 0.116 takes each function's code memory from the
global allocator, so two functions of one JIT module can land any distance
apart. A call that the CLIF marks `colocated` compiles to a pc-relative call
(`bl` on aarch64, ±128 MB; `call rel32` on x86-64, ±2 GB). Beyond that range
the displacement wraps or the relocation asserts (ACT-1070, attributed by
`qa` with the `MALLOC_ARENA_MAX=1` control and closed in S124; its record is
in Git history).

- Every function the backend declares with `Linkage::Local` or `Export` is
  `colocated` when referenced: drop glue, lambda bodies, function-value
  wrappers, continuations, poll functions and trace wrappers. Calls to
  language functions go through the GOT (§1.1) and calls to intrinsics are
  imports, so neither is exposed.
- Data references are not exposed on the supported hosts: aarch64 without
  PIC lowers every symbol address to an absolute literal.
- The object path is not exposed. The in-process linker copies one text
  section into one mapping, and the system linker places one text section.

**Decision: the JIT compiles every call far.** The JIT's module is a
crate-private wrapper over `JITModule`. Its function-definition entry clears
`colocated` on every external function of the context and then delegates.
Upstream does the same for its hotswap mode. A far call is an absolute address
and an indirect branch, so placement cannot put a callee out of reach.

- **Grade: structural.** `Jit` holds only the wrapper and hands it out only
  as `impl Module + CodeFinalizer`, so every function the JIT defines passes
  through the one definition entry. `JITModule` no longer implements
  `CodeFinalizer`, so a module that compiles near calls cannot be passed to
  `compile_to_module`. No emission site can opt out, and none needs to change.
- **CLIF is unchanged** in both modes. The rewrite happens after capture, at
  the fixup boundary (§1.2 row 6). Captured and dumped CLIF still shows
  `colocated` on local callees; the JIT's machine code reaches them far.
- **Cost.** One literal load per call to a compilation-local callee. No
  object, cache or golden-CLIF change, so no `CACHE_SCHEMA_VERSION` change.
- **Unchanged:** `Jit::new`, the ISA flags, the host-symbol lookup, and
  the object path.

**Rejected.**

- *Clear `colocated` in the CLIF, in both modes,* through one declaration
  helper and a lexical census. It needs no public change, but its grade is
  only lexical. It also changes every golden CLIF and makes every local call
  in a cached object a GOT load through the in-process linker, a path the
  defect does not touch.
- *PIC with upstream hotswap.* The JIT's own GOT and PLT entries also come from
  the global allocator, and the `adrp` reaching them has a ±4 GB range. The
  failure class stays and every data reference joins it.
- *A contiguous code arena.* `cranelift-jit` 0.116 offers no memory provider.
  Upgrading Cranelift is a technology selection, which is `arch`'s.
- *Restricting the allocator,* as the control does. It is process-wide,
  glibc-specific and unenforced, so it controls the symptom, not the
  mechanism.

**Public surface.** `Jit::jit_module` returns
`&mut (impl cranelift_module::Module + CodeFinalizer)`, and its rustdoc states
the promise: no call in a function defined through it depends on where the JIT
places code. `JITModule` does not implement `CodeFinalizer`. The wrapper,
`FarCallModule`, is crate-private. In-crate tests read a finalized address
through `CodeFinalizer` or a crate-private accessor on `Jit`.

**Evidence.**

- Module row M-1070-a (`jit/call_reach_tests.rs`) defines a caller with a
  `colocated` call through the wrapper and finds no pc-relative call
  relocation (`Arm64Call` or `X86CallPCRel4`). The same context defined
  through a bare `JITModule` holds one, which shows the row detects the fault.
- A row that places two functions out of range cannot be built
  deterministically on 0.116, because placement is private to `cranelift-jit`
  and follows the allocator. M-1070-a observes the property that makes
  placement irrelevant; `qa` judged it adequate.
- End to end, `spec_07_traits::s124_1070_jit_call_range_subject` passes, with
  `s124_1070_jit_call_range_arena_control` as its control.

**Residual, asserted.** The in-process linker's `adrp` relocation arm
(`apply_elf_aarch64_reloc`, and its Mach-O twin) writes the page delta
without a range check, unlike its `CALL26` arm. A text mapping and the
data or GOT-slot mapping it addresses more than 4 GB apart would be
patched to the wrong page. Anonymous mappings are placed adjacent in
practice, so this is not observed. *Falsifier:* a cache-hit load whose text
and data mappings are more than 4 GB apart. *Trigger:* any change that places
those mappings apart. The remedy is a located error in that arm, matching
`CALL26`.

## Cross-references

- [Bounded contexts](../arch/bounded-contexts.md) — the backend invariants,
  named type-glue access and intrinsics closure-layout contract
- `design/arch/principles.md` Principle 22 — retention ownership for a published
  pointer
- `design/int/session-transaction.md` §6–§7 — the session retention pool
- `module-caching.md` — the cache-hit half of the boundary
- `executable-generation.md` — the `--link` half
- `ring2-rc.md` — the RC conventions, which must emit identically on both paths
