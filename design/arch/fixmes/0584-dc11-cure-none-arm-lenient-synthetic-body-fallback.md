---
number: 0584
target: /arch
filed_by: /dev
filed_at: 2026-07-13
sprint_filed: 109
refers_to: design/arch/dotted-ctor-canonical-keys.md §10.3; crates/cranelisp-backend/src/compiler/match_codegen.rs::compile_constructor_pattern; crates/cranelisp-backend/src/lib.rs::lenient_mono_from_expr
status: open
---

# §10.3 "None → hard CodegenError, never a fallback" is insufficient for the lenient/synthetic-body path

**Context (W1.2 DC-11 cure, landed).** §10.3 rules that pattern position gets
exactly ONE resolver: `compile_constructor_pattern` reads the arm's
`resolved_ctor` by direct keyed read (`ctor_meta_at`), and a `None` (or probe
miss) is a **hard `CodegenError`**, `lookup_constructor` never called from
pattern position again. §10.2 threads `pattern_ctors` only into
`MonoExpr::from_expr` (the `codegen_view` builder).

**The gap.** `codegen_view` is `None` for a whole class of legitimately
non-body-AST-typed entries — **auto-generated field accessors** (whose synthetic
body is `(match self [(Box v) v])`, a `Pattern::Constructor` arm), R5
value-layout construct/extract matches, generic templates, REPL `__expr`. These
compile through **`lib.rs::lenient_mono_from_expr`** (the signature-driven /
lenient builder), which has **no `pattern_ctors` sidecar** — its ctor arms are
built `resolved_ctor: None`. Making `None` a hard error (as §10.3 literally
states) **breaks these paths** — empirically verified: the strict `None → error`
variant reds `display_exact::{display_r5_value_layout_*, r5_value_layout_construct_match_extract_is_sound, …}`
and the field-accessor suite. These ctors are single **in-scope-unambiguous**
names (a product ctor `Box`, a template ctor) — never scrutinee-directed
same-named ctors, which exist ONLY in user `defn` bodies (→ `codegen_view` →
populated `resolved_ctor`).

**What landed (the deviation).** `compile_constructor_pattern`:
`Some(fq)` → `ctor_meta_at(fq)`, and a `Some` that resolves to **no `Def` is a
hard `CodegenError`** (keying drift — the loud miss §10.3 wants, pinned by BU-1
`ctor_meta_at_keyed_read_hits_real_def_and_misses_are_loud`); `None` →
**`lookup_constructor`** (the ONE narrow, deterministic fallback for the
in-scope-unambiguous synthetic/lenient ctor). The DC-11/12/13 cure is intact:
scrutinee-directed contested ctors carry a `Some` and take the keyed read;
`lookup_constructor` is reached only where its context-free resolution is
correct-by-construction (single in-scope candidate). BU-1 therefore pins the
`Some`-that-misses loud error rather than the `None` one.

**Ask (`/arch`).** Ratify the deviation as the settled §10.3 end-state, OR
choose the stricter alternative and design its cost: thread the sidecar (or a
`CompileContext`-supplied context-free storage-key resolver) into
`lenient_mono_from_expr` so every ctor arm carries a `Some` and `None` can be
the hard error uniformly. The stricter path is more plumbing (recursive
threading of a resolver into the lenient builder + a `CompileContext` field);
the landed fallback is smaller and correct for the tested surface. Either way,
§10.3's prose ("`None` → hard error, never a fallback") needs correcting to name
the lenient/synthetic-body `None` as legitimate.
