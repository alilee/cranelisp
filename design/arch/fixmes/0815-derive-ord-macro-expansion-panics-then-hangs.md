---
number: 0815
target: /qa
filed_by: /stdlib
filed_at: 2026-07-21
sprint_filed: 115
refers_to: stdlib/derive.cl:39 (derive-Ord); stdlib/derive/helpers.cl:251-269
  (build-later-arms / build-ord-enum-lt-go / build-ord-enum-lt-arms);
  spec/09-macros.md §9.3 (macro expansion); stdlib/plan-stdlib.md §26.4
status: open
---

# `derive-Ord` panics during macro expansion at 2 constructors and HANGS deterministically at 3

## Issue

`derive-Ord` is non-functional on the simplest possible input — a nullary enum —
and the failure MODE changes with the constructor count. Probed at HEAD
(2026-07-21, `target/release/cranelisp`, **pristine working dir per run**: fresh
directory, no persisted `user.cl`, no `.cranelisp-cache`,
`CRANELISP_LIB=/home/alilee/cranelisp/stdlib`).

**1 constructor — expansion completes, conformance rejects:**

```
(import [derive [derive-Ord]])
(import [compare.ord [Ord <]])
(derive-Ord (deftype T A))
⇒ Error: type error at 0..26: impl Ord for T: missing required method <=
```

(That reject is a separate **stdlib-side** gap — `derive-Ord` emits only `<` and
`>` while `Ord` requires four methods. `/stdlib` owns and fixes that. It is
included here only because it proves the expansion machinery itself runs on the
1-ctor input, which is what makes the 2- and 3-ctor results anomalous.)

**2 constructors — runtime panic inside expansion:**

```
(derive-Ord (deftype T A B))
⇒ Error: macro error at 0..28: macro `derive/derive-Ord` aborted at 0..28:
   runtime error during macro expansion: runtime panic: match failed
```

**3 constructors — deterministic HANG:**

```
(derive-Ord (deftype T A B C))
⇒ (no output; no further prompt; killed at 40s, and at 90s, and at 120s)
```

The hang reproduced **3/3** at 90s in the original probe and again at 40s in the
pristine re-run. One earlier run of the same input via the `derive` dispatch
macro produced `runtime error during macro expansion: bus error` instead of
hanging, so the 3-ctor cell has at least two observed faces (hang, SIGBUS).

## Why /stdlib cannot attribute this

The two candidate owners are (a) an infinite recursion / partial `match` in
`stdlib/derive/helpers.cl`, which is **/stdlib's own bug**, and (b) the
macro-expansion runtime. I could not separate them, for a reason that is itself
the finding:

- **A macro-expansion `runtime panic: match failed` names no location inside the
  macro.** The span reported (`0..28`) is the CALL SITE. There is no indication
  of which `match` in which helper failed, so the panic cannot be localised by
  reading the message.
- **A hang emits nothing at all** — no partial expansion, no progress signal.
- I inspected the obvious suspects and they look total/bounded: `snth`
  (`helpers.cl:32`) has both `SNil` and `SCons` arms; `build-later-arms`
  (`helpers.cl:251`) counts `j` up to `len` and is called with `j = idx+1 ≤ len`.
  So the bug is not where a reading of the source puts it, which is exactly when
  a seam observation is needed rather than more source-staring.

The load-bearing evidence for (b) is the **1-ctor cell**: the identical code path
(`build-ord-enum-lt-arms` → `build-ord-enum-lt-go` → `build-later-arms`) runs to
completion and produces a well-formed impl. A stdlib-side infinite recursion that
only appears at n=3 while n=1 completes and n=2 panics is possible but is not the
shape a bounded index loop produces.

## Request

1. `/qa` attributes (stdlib helper vs macro-expansion runtime) and routes.
2. `/testing` lands the three cells above as a repro family — they are three
   one-liners with two imports and no fixtures. **The 3-ctor cell must carry a
   timeout**, not a plain assertion; a hang in the suite is worse than a RED.
3. Independently of attribution: **a macro-expansion panic should name the
   position inside the macro body**, not only the call site. Without it a macro
   author cannot debug their own expansion — this is the usability half and it is
   what made this a /qa handoff instead of a /stdlib fix.

## Context

Found by `/stdlib` during the S115 Phase-6a assessment sweep of the modules that
carry **no self-tests**. `derive.cl` is one of 12 such modules; `plan-stdlib.md`
§26.4 records that the derive self-test home must be a downstream consumer module
that derives on its own ADT, and that module was never built. Every derive defect
in this FIXME and in 0816 would have been caught on the day it appeared by that
missing test module. `/stdlib` is building it in 6b.
