---
number: 0484
target: /design
filed_by: /arch
filed_at: 2026-06-30
sprint_filed: 97
refers_to: design/platform/poll-support.md §3.5.1 (lines ~748-783 — the `## Opacity` block + the `web/Connection` deftype comment)
status: open
---

# Re-word `Connection` opacity — it is opaque to the TRAMPOLINE, NOT to the user

## Issue

`design/platform/poll-support.md §3.5.1` carries the misleading framing that the
`Connection` handle is opaque **to the user**:

- L758-760: "`Connection` is an **opaque ADT**: the `fd` field is **present but not
  user-destructurable** — user code threads the handle from `accept` to
  `read`/`send`/`close` but cannot pattern-match it open to read or forge the fd."
- L761-762: "Opacity is expressed per `/arch`'s ruling on opaque ADTs (the field is genuine
  program/platform data; **the type does not export a user destructuring path**)."
- L749-750 (the deftype comment): "the connection fd lives in an ordinary opaque ADT field
  the PLATFORM reads back ... the trampoline never introspects it." (This half is correct.)

This wording attributes a "no user destructuring path" invariant to `/arch`. **That
attribution is wrong** and was the basis for the S97 Wave-2 STOP on QA test 2.1
(`…not_user_destructurable`), which asserts a non-invariant. There is no mechanism in the
language to make an ADT non-user-destructurable, and `/dev` correctly declined to invent one.

## Proposed resolution

The user clarified the intent (2026-06-30): the handle is opaque **to the trampoline /
runtime**, NOT to the user. `/arch` has corrected its owned docs accordingly
(`effect-concurrency.md §4.1.1`, `bounded-contexts.md §5`, `interfaces.md §"Resource
scheduling"`): the handle is **tramp-opaque, user-readable**.

Re-word §3.5.1 so it states:

1. **Tramp-opacity** (the real, load-bearing invariant — keep this): the *trampoline*
   never introspects the handle; only the *platform* reads `r`/`fd` back out of it. This is
   what lets all scheduling live in the `ctx` vtable.
2. **User-readability** (the correction): the user program CAN read the handle's genuine
   fields (fd, peer addr) by ordinary destructuring / `match` — `(match c [(Connection fd)
   fd])` typechecks and yields the real fd. It is the program's own connection. Drop the
   "present but not user-destructurable" / "does not export a user destructuring path"
   claims and the `TcpStream` "no user reads directly" analogy (invert it: it is
   `TcpStream` with `as_raw_fd()` *available*).
3. **Fabrication** (so the doc is complete): user *construction* of a handle is a
   platform-IO concern, not a host-soundness one — the OS syscall is the capability
   checkpoint; a bad/unowned fd errors safely (`EBADF`-class IO error, recoverable at
   `catch-runtime-error`), never host UB. `/arch`'s full ruling is in
   `effect-concurrency.md §4.1.1` ("Handle fabrication is a platform-IO concern…"); cite it
   rather than re-deriving.

## Operational implication / Context

- The `/qa` test 2.1 (`connection_..._not_user_destructurable_neg`) tests a non-invariant
  and is being RETIRED / inverted to a positive user-readability test by `/qa` (per `/arch`
  ruling this sprint). The real scheduling-opacity invariants are covered by 2.5
  (`carries_no_scheduling_state`) + the backend CLIF-absence unit. So this re-word removes
  the *only* doc the failing assertion pointed to.
- `/dev`'s as-built `Connection [:primitives/Int fd]` (ordinary destructurable 1-field ADT)
  is **correct** and stays.
- Scope is wording-only; no design/shape change. `web.cl`/`serve.cl` split, the load-order
  rule (§3.6.3), and the singleton stdin token (§3.1) are untouched.
