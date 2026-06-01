---
number: 0247
target: /arch
filed_by: /dev
filed_at: 2026-06-01
sprint_filed: 73
refers_to: design/arch/facades/primitives.md §"Public surface"(line 24)/§"Removed from pub surface (S68 narrowing)"(line ~191 "#[used] discipline"), design/primitives/primitives.md §"Step 5 — Triage close (FIXMEs 0182, 0212)", design/arch/fixmes/0212 (Option 1), crates/cranelisp-primitives/src/{ring0,int,float,bool,marshal,string,vec}.rs
status: open
---

# `#[used]` is not applicable to `extern "C" fn`s — the facade-prescribed DCE-prevention mechanism does not compile

## Issue

The binding facade `facades/primitives.md` §"Public surface" (line 24) and the
`/design (primitives)` plan (Step 5, resolving FIXME 0212 via Option 1) prescribe
adding `#[used]` to each `pub(crate) extern "C"` primitive fn to prevent dead-code
elimination of the fns in `--link`-mode static archives.

**This does not compile.** Rust's `#[used]` attribute applies **only to `static`
items**, never to functions. Attempting it on the primitive extern fns yields:

```
error: `#[used]` attribute cannot be used on functions
   = help: `#[used]` can only be applied to statics
```

(Confirmed on this crate's edition-2024 build with rustc; 45 occurrences, one per
extern fn, all rejected.)

So FIXME 0212 Option 1 as written is not implementable. The `/dev (primitives)`
Wave-2 work landed everything else (backend sever, `code: None` builder adoption,
layout dedup, unit harness, FIXME 0182 close) but **could not add `#[used]`**. The
extern fns currently carry only `#[unsafe(export_name = "…")]` (as they did before
this sprint).

## Why the symbols survive today anyway

The crate builds as a JIT-mode dependency and the GOT is populated at static-init
from the in-crate `extern_shims()` harvest (`lib.rs`), which takes each fn's address
(`ring0::add_i64 as *const u8`). Taking the address in `extern_shims()` is itself a
use that keeps the fns alive in the normal (rlib/JIT) build — which is why the crate's
71 unit tests pass and the GOT slots are populated. The DCE concern is specific to
`--link`-mode **static-archive** linking, where the linker may drop archive members
with no external reference.

## Proposed resolution (for /arch — pick one)

1. **Amend the facade to name a `#[used]`-on-static mechanism.** Since `#[used]`
   only attaches to statics, the canonical DCE anchor is a single `#[used] static`
   that references each fn pointer — effectively `extern_shims()`'s harvest promoted
   to (or mirrored by) a `#[used] static FORCE_LINK: [*const u8; N] = [add_i64 as _, …]`.
   The facade §"Public surface" line 24 and §"Removed from pub surface" `#[used]
   discipline` note would be rewritten to "a single `#[used]` static array referencing
   every extern fn ptr (the `extern_shims()` harvest is the natural carrier)".
2. **Amend the facade to rely on `#[unsafe(export_name)]` + the exe-bundle force-link
   line.** The cascade pointer in `facades/primitives.md` §"Cascade pointers"
   (exe-bundle / `cranelisp_init_primitives()`) already calls for a startup
   `LazyLock::force(&PRIMITIVES_TABLE)`; forcing the static takes every fn address via
   the harvest, which may suffice as the link anchor without any `#[used]`. If so, the
   `#[used]` discipline language is simply struck from the facade.

Either resolution is `/arch`'s call (facades are `/arch`-owned). `/dev (primitives)`
cannot edit the facade and will not improvise a different DCE mechanism without the
facade naming it. When `/arch` selects, `/dev (primitives)` implements (e.g. adds the
`#[used] static` array in `lib.rs`) and the doc-comments in `lib.rs` (currently
pointing at this FIXME) update to match.

## Operational implication / Context

- Non-blocking for Wave 2's other deliverables — all landed and green (71 tests pass,
  crate builds independent of backend, baseline regenerated).
- Blocking for `--link`-mode static-archive correctness (FIXME 0212's actual concern).
  Until resolved, `--link` builds risk DCE-dropping unreferenced primitive archive
  members. The `cranelisp_init_primitives()` exe-bundle force-link work (a future
  `/dev (binary)` / `/dev (intrinsics)` step per §"Cascade pointers") is the natural
  place to verify the anchor actually holds.
- FIXME 0212 should be re-dispositioned by `/arch` (Option 1 is void; Option 2 — name
  `extern_shims()`'s static-data reference as the canonical DCE mechanism — looks
  correct and matches resolution (1)/(2) above).
