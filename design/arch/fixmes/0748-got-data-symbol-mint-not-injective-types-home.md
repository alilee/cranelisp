---
number: 0748
target: /arch
filed_by: /dev (cranelisp-backend, S115 W3)
filed_at: 2026-07-21
sprint_filed: 115
refers_to: crates/cranelisp-types/src/module.rs::got_data_symbol_name; design/arch/safety-invariants.md §4 R4; design/backend/s115-carrier-and-rc-sweep.md §4
status: open
---

# R4: the GOT data-symbol mint is non-injective, and its canonical home is `cranelisp-types` — the fix cannot land backend-side

## Severity
Important (a constructible cross-module wrong-slab dispatch; the R4 census's ONE
backend-facing owed witness, blocked on a types edit).

## Issue

`design/backend/s115-carrier-and-rc-sweep.md` §4 names `got_data_symbol_name` as
the single backend-owned OWED-witness and assigns `/dev` to "build an injective
flatten + a round-trip witness". Executing that in W3 surfaced two facts.

### 1. The defect is real and constructible

The mint flattens the module path with `.`→`_`:

```rust
let flat = module_path.as_ref().replace('.', "_");
format!("__cranelisp_got_{}", if flat.is_empty() { "_entry" } else { &flat })
```

Module paths admit `_` **and** `.`, so the two-component path `a.b` and the
one-component module `a_b` both mint `__cranelisp_got_a_b`: two modules share ONE
GOT slab data symbol. Every cross-module GOT-indirect call from either module
then relocates against the other's slab — the R4 class one level up from the
drop-glue keying defect (0633/0640), with the same silent-wrong-target shape.
Pinned as the standing witness in
`compiler::resolution::tests::got_data_symbol_name_collision_is_the_owed_r4_witness`
(currently an `assert_eq!` on the collision, to INVERT to `assert_ne!` in the
fixing change-set).

### 2. The mint lives in `cranelisp-types`, and the backend is only a CONSUMER

`cranelisp_types::got_data_symbol_name` (`module.rs:2569`) is the canonical home
— relocated DOWN from backend at S76 by /arch review, with its rustdoc stating
the reason: the scheme is consumed by two crates, so it must not be duplicated.
The **definers** all call the types-owned fn:

- `crates/cranelisp-backend/src/jit.rs:264` (JIT `symbol_lookup_fn` registration)
- `src/worker.rs:1610` (cache-hit `Linker::register_symbol`)
- `src/exe.rs:862` (`--link` relocation)

while the backend CONSUMER emits the `Linkage::Import` reference
(`compiler/control_flow/fn_as_value.rs`, `compiler/mod.rs`).

The S76 relocation, however, left a **live duplicate body** behind at
`cranelisp-backend/src/compiler/resolution.rs::got_data_symbol_name`. W3 changed
that copy alone to the injective escape and the result was immediate and total:

```
can't resolve symbol __cranelisp_got_compare_dord
can't resolve symbol __cranelisp_got_fn_doption_dtest
… the entire stdlib fails to load; 40+ e2e REDs
```

— the consumer emitted relocations against names the definer never registered.

**Landed in W3 (backend-side, P7):** the duplicate body is deleted; the backend
fn is now a one-line forward to the types-owned home, fenced by
`resolution::tests::got_data_symbol_name_agrees_with_the_types_owned_home`
(a corpus equality assertion that fails on any future one-sided change). The
injectivity fix itself is NOT landed — it is yours.

## Proposed resolution

An injective, prefix-free mint at the types home. The live in-tree injectivity
model is now `cranelisp_types::drop_glue_symbol_name` (`module.rs:2654` —
length-prefixed hex components, prefix-free/injective by construction, pinned
by the `module/tests.rs` battery). *(Stale-citation repair, /arch S118 W8: this
section originally named `cranelisp-backend`'s `escape_symbol` as the proven
scheme; that fn was DELETED at S118 W3 §8 with the backend-local glue-naming
home — its escape scheme (`_`→`__`, `.`→`_d`, `-`→`_h`, `_u{cp:06x}` catch-all,
total decoder) is recoverable from git history. NOTE for the implementer:
length-prefixed hex does NOT keep alphanumeric paths as fixed points, so it
cannot be reused verbatim here — constraint 1 below still binds; recover the
escape scheme or design a fixed-point-preserving variant.)* Two shapes:

- **(a)** move/duplicate that escape into `cranelisp-types` beside
  `got_data_symbol_name` and apply it to the path (a types edit + a
  `public-api.txt` delta if the escape is exported); or
- **(b)** a narrower types-local escape sufficient for module paths (the reader's
  legal module-name charset is much smaller than `render_type`'s).

**Binding constraints for whichever shape lands:**

1. **Purely-alphanumeric paths MUST stay fixed points.**
   `__cranelisp_got_primitives` is an `export_name` LITERAL in
   `cranelisp-primitives/src/lib.rs:143` and is linked against by every `--link`
   binary; the deleted `escape_symbol` scheme satisfied this by construction
   (a property the landed mint must preserve). Pinned by
   `resolution::tests::got_data_symbol_name_matches_the_pinned_link_time_abi_literals`.
2. **One change-set, one scheme.** Definers and consumer all route through the
   types fn today, so a single edit moves them together — but the cached `.o`
   corpus and any `--link` prereq fixtures bake the old names. `BUILD_ID`
   invalidates `.meta.json`, and `tests/scripts/build-link-prereqs.sh` rebuilds
   the link fixtures; confirm both before landing.
3. The `_entry` sentinel for the empty path must stay outside the escape image.

## Context

Also recorded by the §4 census: the two *other* R4-owed families mint outside
this crate — the platform export names (`cranelisp-platform`, uniqueness-keyed)
and typecheck's `$`/`+`-joined LinkerSymbol/method mangle. Both are routed to
their own homes there; this FIXME is only the GOT-slab family.
