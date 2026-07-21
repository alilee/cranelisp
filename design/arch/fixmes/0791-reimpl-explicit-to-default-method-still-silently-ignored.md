---
number: 0791
target: /dev (src)
filed_by: /review
filed_at: 2026-07-21
sprint_filed: 115
refers_to: src/worker.rs::derive_codegen_batch TopLevel::TraitImpl arm (the S115 W6
  mangled-method enrollment, fab0b9ac) vs spec/05-definitions.md §5.4.5 +
  spec/07-traits.md §7.1.5 — a re-impl that OMITS a method the prior impl
  overrode keeps dispatching the STALE override instead of the trait default.
status: open
---

# The re-impl hot-reload closes the explicit→explicit case but NOT explicit→default — the stale override survives

## Severity
Important (spec violation, same silent-ignore class as the defect W6 fixed; narrow
sequence, not a regression — RED before and after W6)

## Issue

The W6 fix enrolls the impl's mangled method `Def`s into the FORCED loop by
iterating **`impl_.methods`** — the methods the new `impl` block *explicitly*
provides:

```rust
let mangled: Vec<Symbol> = impl_
    .methods
    .iter()
    .flat_map(|method| {
        let prefix = format!("{}.{}$", impl_.trait_name, method.name);
        ...
```

A method the new impl **omits** is therefore never enrolled. Per spec §7.1.5
("Methods with defaults are automatically synthesized if not explicitly
provided") + §5.4.5 (a re-impl **REPLACES** the previous implementation), a
re-impl that drops an override must fall back to the trait's **default** body.
It does not: `impl_check.rs`'s default-synthesis loop (~`:1120`) does re-stage
the default `Def` (the re-impl's `provided` set no longer contains the method),
`commit_slotted_def` classifies it `AbiPreserving` and carries the prior code
over, the FORCED loop skips it (not in `impl_.methods`), and the
`already_compiled`-gated sweep skips it too — the exact chain
`impl-redefinition-hot-reload.md` §2 describes, one method-source away.

## Repro (verbatim, `/review` W6 probe, HEAD `7a09e86b`, scratch cwd)

```
(deftype Box (Bx [:Int v]))
(deftrait Sizeable (size [x] Int) (weight [x] Int 100))
(impl Sizeable Box (defn size [x] 12) (defn weight [x] 55))
(size (Bx 0))     ; => :primitives/Int 12
(weight (Bx 0))   ; => :primitives/Int 55
(impl Sizeable Box (defn size [x] 7))     ; weight OMITTED -> trait default 100
(size (Bx 0))     ; => :primitives/Int 7   (correct — W6's fix)
(weight (Bx 0))   ; => :primitives/Int 55  WRONG; MUST be :primitives/Int 100
```

The **reverse direction works**, which localises the fault precisely: first impl
omits `weight` (dispatches the default `100`), re-impl provides `(defn weight [x] 55)`
→ dispatches `55`. `weight` is in `impl_.methods` on that re-impl, so it enrols.

## Proposed resolution

Drop the per-method narrowing and enrol every mangled method `Def` of the
trait in the writer's live table — i.e. match on the `{impl_.trait_name}.`
prefix + a `$` suffix rather than `{trait}.{method}$`. That is the same
over-enrolment tradeoff the arm's own comment already accepts and justifies
("a sibling impl of the same trait+method for a different type may be
co-enrolled, which costs a recompile and changes nothing observable"), and it
keeps int out of the resolution business (Principle 24). Alternatively enrol
the trait's DECLARED method set, but that requires reaching the trait decl —
which may be homed in another module (D45), so the prefix scan is the cheaper
and more structural answer (Principle 18).

**Test obligation (METHOD §2.2, both tiers):** the unit pin at
`derive_codegen_batch` must add a cell whose `TraitImpl` fixture omits a
method that has a live mangled `Def` carrying `code: Some(_)`, asserting it is
still enrolled (fail-on-revert against the shipped `impl_.methods` loop); the
e2e above belongs with the S115 W6 dispatch pin (`/testing`, alongside FIXME
0790's sharpening).

## Context

`/review`(src) S115 W6, change-set `fab0b9ac`. Boundary probing of the
impl-redefinition fix per the W6 review brief. The other four boundaries the
design did not enumerate all **PASS**: multi-method re-impl (both methods
reload), two-target trait (re-impling one leaves the other intact), a
cross-module impl (trait in `tlib`, impl written in `user`; and an impl written
in a `/mod sub` namespace), and re-impl in a cache-restored session. This is the
one hole.

Attribution is `/dev`(src) — `impl_check.rs` already re-stages the default
`Def`, so the miss is in the int-side enrollment, not typecheck. If a trace
shows the default is NOT re-staged on re-impl, the fork moves to
`/dev`(typecheck) with this repro as the brief.
