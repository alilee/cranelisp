---
number: 0573
target: /dev
filed_by: /repl
filed_at: 2026-07-12
sprint_filed: 108
refers_to: the REPL session backing-file write path (src/ session layer,
  session_v4 + design/int/session-persistence.md) — a product-form
  `(deftype Name [:Int field])` definition is accepted and usable in-session but
  is NOT appended to the backing `.cl` file, whereas a sum-form
  `(deftype Name (V1 …) (V2 …))` is. Reproduced post-S108.
status: open
---

# Product-form `deftype` is not persisted to the backing source file

## Issue

A sum-form `deftype` is written to the backing file; a product-form `deftype`
entered immediately after is accepted, works fully in-session, but never reaches
the file:

```
> (deftype Rotation (L [:Int steps]) (R [:Int steps]))
:user/Rotation ; deftype
; match:
;  L R
> /sh cat .proj7/user.cl
(deftype Rotation (L [:Int steps]) (R [:Int steps]))          ; <-- persisted

> (deftype Position [:Int pos])
:(Fn [primitives/Int] user/Position) user/Position ; deftype  ; <-- accepted
> pos
:(Fn [user/Position] primitives/Int) user/pos ; defn - Canonical field accessor …
> /source Position
; source for Position
(deftype Position [:Int pos])                                 ; <-- source IS captured in-session
> /sh cat .proj7/user.cl
(deftype Rotation (L [:Int steps]) (R [:Int steps]))          ; <-- Position MISSING from the file
```

`Position` is fully live in the session — its constructor typechecks, its `pos`
accessor exists, and `/source Position` reconstructs it — yet `.proj7/user.cl`
still contains only `Rotation`. The single differentiator is the **deftype
shape**: `Rotation` is a multi-variant **sum** form; `Position` is a
single-**product** form (`[:Int pos]`, the type name doubling as the
constructor). The write path persists the sum form and skips the product form.

## Assessment (severity: medium-high — silent data loss / persistence divergence)

This is a **defect**, and a nasty one because it is silent: the definition
succeeds, the REPL reports success, but the durable project file is incomplete.
On the next session load / replay the backing file is the source of truth, so
`Position` (and its accessor, and anything downstream) simply vanishes — the
reloaded session diverges from the one the user built. This is exactly the
REPL/persistence divergence class we treat as a serious red flag (session
persistence must be one shared path, not per-form).

Note the in-session source store and the backing-file write are clearly
**different paths** — `/source Position` works (source captured) while the file
write missed it. Whatever records source for `/source` handles both deftype
shapes; the file-append path does not.

## Proposed resolution

- **/dev (src/ session layer)** — find *why* the backing-file write skips the
  product-form `deftype`. Get call-chain evidence first (which persistence hook
  fires for the sum form and not the product form) before changing anything —
  do not patch the symptom. The fix must route **all** definition forms through
  the one persistence path so in-session state and the backing file cannot
  diverge by deftype shape. Cross-check `--run`/`--link` replay of a backing
  file containing a product deftype.

**This is a DEFECT** — it requires a failing-not-ignored `/testing` repro: after
defining a product-form `deftype` in a session with a backing file, the backing
file must contain that definition (and a reload must retain the type + its
accessor). This FIXME is the scoping record until that repro lands, then it is
deleted (the failing test is the durable record + trigger).

## Notes

- Secondary observation from the same transcript, likely a *different* store to
  cross-check while here: `/sexp Rotation` → `Error: no sexp available for
  'Rotation'` even though `/source Rotation` works. So the sexp store and the
  source store also disagree for a sum-form deftype. Minor, but it points at the
  same "multiple per-form stores that don't agree" smell — worth confirming it is
  or isn't the same root cause. Do not let it expand the defect's repro scope;
  file separately if it proves independent.
