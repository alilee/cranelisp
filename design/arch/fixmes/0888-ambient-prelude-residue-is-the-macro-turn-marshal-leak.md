---
number: 0888
target: /sprint (scope arbitration — the user decides fix-vs-carry per
  tests/plan/s118-test-plan.md §2.5 Branch F; if a fix window is opened the
  routing is /design(int) protocol ruling first, then /dev(int))
filed_by: /qa
filed_at: 2026-07-26
sprint_filed: 118
refers_to: src/marshal.rs (the int-side macro-expansion marshaller — the
  by-design leak, header lines 1–18, and protect_marshalled_cell FIXME-0638
  deep protection); src/expander.rs:512-549 (invoke_clause — marshals args,
  never releases them, never consumes the expansion-result tree after
  runtime_to_sexp); design/arch/fixmes/0835-* (the falsified prior
  attribution — prelude face); tests/plan/s118-test-plan.md §2.5 (Branch F,
  plan of record); baseline cells #10/#19/#20/#21/#23
status: open
---

# The ambient prelude-load residue (1143) is the macro-turn marshal leak in `src/marshal.rs` — by-design, int-owned, NOT the 0835/RE runtime-pair class

## Attribution (S118 Branch-F falsification probe, /qa, 2026-07-26, HEAD `34aac8ff` post-W2b)

The program-independent residual every stdlib-prelude `--run` child carries is
the **documented, deliberate compile-time leak of the int-side
macro-expansion marshal boundary**:

1. **Args are leaked by design.** `src/marshal.rs` header: "Marshalled values
   are 'leaked' — their RC is never decremented, since they exist only during
   compilation." Every marshalled cell additionally takes the FIXME-0638
   deep-protection `+1` (`protect_marshalled_cell`) so the consuming clause
   can never free it. Nothing ever releases the arg trees or the args-SList
   spine built in `invoke_clause` (`src/expander.rs:526-530`).
2. **The expansion-result tree is never consumed.** `invoke_clause` copies the
   returned runtime Sexp tree into a compiler `Sexp`
   (`marshal::runtime_to_sexp(result_i64)`, `expander.rs:548`) and then drops
   the `i64` on the floor — no `consume_sexp`, no release of the JIT-built
   result cells.

Residual model, exact on every measured point: **residual = |heap cells in
the marshalled arg trees + args spine| + |heap cells in the returned result
tree not aliasing a marshalled cell|, summed over expansions.** Zero quote
forms required; linear in expansion count and in sexp size; constant type
depth — the signature that was previously read as 0835's.

## Probe table (fresh tempdir + `env -i` allow-list per child, `--run
--no-cache`, `CRANELISP_RC_STATS=1`, trivial `Int` child, debug binary)

| shape | macro body | predicted | measured |
|---|---|---:|---:|
| P0 empty prelude | — | 0 | 0 |
| P2 defmacro defined, never invoked | `` `~x `` | 0 | 0 |
| ctor-macro defined, never invoked (control) | `(SexpInt 2)` | 0 | 0 |
| P3 `(ident 41)` | `` `~x `` | 2 = arg cell + spine SCons | **+2** |
| P3b two invocations | `` `~x `` | 4 | **+4** |
| P3c `(ident (add-i64 (add-i64 1 2) (add-i64 3 4)))` | `` `~x `` | 23 = 22 arg-tree cells + 1 spine (result aliases arg) | **+23** |
| **(d) NO quote forms, nullary** `(two)` | `(SexpInt 2)` — ctor-built | 1 = result cell, zero args | **+1** |
| **(d)+(b) NO quote forms, list result** `(three)` | `(SexpList (SCons (SexpSym "add-i64") …))` | 8 = result-tree cells | **+8** |
| **(a) quote-built, IDENTICAL result** | `` `(add-i64 1 2) `` | 8 (quote path balanced ⇒ equal) | **+8** |
| P4 full stdlib | — | Σ over prelude-closure expansions | **1143** |

Discrimination within the macro-expansion turn is total:

- **(d) a macro with NO quote form anywhere still leaks** — the producer is
  NOT the `quote_sexp`/`quote_slist` path.
- **(a) quote-built vs constructor-built identical result are EQUAL** — the
  primitives-side quote path contributes zero marginal residue (its RE-3
  audit verdict is confirmed empirically).
- Nullary invocation isolates the **result-tree face** (+1 with zero
  marshalled args); `(ident 41)` isolates the **arg-marshal face** (+2 with
  an aliased result).

## Surviving-allocation fingerprint (armed `CRANELISP_ALLOC_PARITY=1` lanes)

- P3 minimal shape: exactly 2 survivors — `size=40 payload@16=0x1` (the
  args-spine `SCons`) + `size=32 payload@16=0x0` (the marshalled `SexpInt`
  arg cell).
- Nullary ctor shape: exactly 1 survivor — `size=32 payload@16=0x0` (the
  JIT-built `SexpInt` result cell).
- Full stdlib: `delta=1143`, dump capped at 64 samples, **all 64 are
  Sexp-family cells**: 26 SCons, 11 SexpList, 7 SexpSym, 5 SexpInt,
  3 SexpStr, 2 SexpBool, 2 SexpBracket, 1 SexpAnnotated, 7 HeapStrings.
  Zero foreign allocation types in the sample.

## What this changes

- The 0835 scope note's "prelude face is THIS defect's face until falsified"
  is **falsified** (the W2b byte-identical P-ladder was the first half; this
  probe names the true seam). 0835 carries a pointer note; its remaining
  faces (B3 residual-2, abort face) are separate.
- Baseline cells #10/#19/#20/#23 measure ONLY this leak; #21 carries it as
  its 1143 ambient term. None can flip from any currently-scoped S118 track
  (plan §2.5 Branch F confirmed).
- This is **not a runtime RC-protocol violation**: user-program execution is
  balanced (P1/P2 = 0). The leak is compile-time, bounded per session, and
  documented — its *cost* is that it poisons the exit-balance instrument
  (RC_STATS / M3 parity) for every stdlib-prelude child, which is the
  memory-safety certification instrument.

## Fix-shape estimate (recommendation input, not a ruling)

- **W2b-shaped (bounded, hours): make the instrument truthful.** Segregate
  marshal-boundary allocations into their own counter bucket (int/intrinsics
  seam) so RC_STATS balance asserts over runtime allocations only — or give
  the five cells a macro-free/mini-prelude twin-control accounting. Bounded
  producer-side change, no ownership-protocol design; but it *accepts* the
  leak as designed behaviour and must be an explicit user acceptance, since
  every future exact-balance cell inherits the ambient term otherwise.
- **W3c-shaped (a wave): true balance at the macro-turn boundary.** Define
  the ownership protocol: post-turn deep-release of the marshaller's
  retained arg trees + consume of the expansion result after the copy,
  handling result↔arg aliasing (the `` `~x `` case where the result IS a
  marshalled arg cell) — or an epoch/arena-scoped expansion allocator freed
  at turn end. The FIXME-0638 history (interior-alias double-free from a
  shallower protection scheme) shows naive releasing has already burned
  once; this needs a /design(int) ruling before any /dev change.

Probe harness retained at the session scratchpad `probe/` tree
(`run_probe.sh` + `lib_*` mini-prelude fixtures incl. the new
`lib_noquote0` / `lib_noquote_list` / `lib_quote_list` /
`lib_noquote_defonly` shapes).
