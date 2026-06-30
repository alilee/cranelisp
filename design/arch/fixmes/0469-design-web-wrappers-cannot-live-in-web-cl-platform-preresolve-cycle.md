---
number: 0469
target: /design
filed_by: /dev
filed_at: 2026-06-29
sprint_filed: 96
refers_to: design/platform/poll-support.md §3.5.1/§3.5.3/§3.5.7, exemplar/web.cl, exemplar/serve.cl, src/platform.rs::referenced_sig_modules
status: open
---

# `poll-support.md §3.5.3`'s "wrappers in `web.cl`" depiction is unrealizable — the platform-load pre-resolve forms a load cycle

## Issue

`poll-support.md §3.5.1/§3.5.3/§3.5.7 step 1` direct `/port` to put BOTH the
connection-handle ADTs (`web/Listener`, `web/Connection`, …) AND the
destructuring wrappers (`listen`/`accept`/`read`/`send`) in **`exemplar/web.cl`**,
with `web.cl` carrying `(import [platform.web [bind-listener accept-conn read-conn
send-conn]])`.

This does not compile. Loading the `web` platform DLL **pre-resolves the external
`.cl` type-modules its sigs reference** before the platform is registered
(`src/platform.rs::referenced_sig_modules` / `platform-interface.md §7.2`). The
web sigs reference `web/Listener`/`web/Connection`/`web/Request`/`web/Response`,
so `(platform web)` fully loads + typechecks the `web` module **first**. If `web`
imports `platform.web`, that import resolves against a platform that is **not yet
registered** → a hard `ModuleError`:

```
module 'web' failed: module 'platform.web' not found (imported by 'web')
```

(Confirmed empirically this wave: `(platform web)` then `/platform-schema web`
failed at the `(platform web)` step with exactly this message until the
`platform.web` import was removed from `web.cl`.)

So the sig-referenced type-module (`web`) **cannot itself reference the platform**
— neither via `(import [platform.web …])` nor via an FQ `platform.web/…` call (FQ
auto-load would try to load `platform.web` as a `.cl` module mid-platform-load,
the same cycle).

## Proposed resolution (and what `/dev`+`/port` shipped this wave)

The interface is unchanged (the ADTs, the leading-pair convention, the poll-leaf
sigs, the serve-loop reshape all stand). Only the **module placement** of the
wrappers moves, within `/port`'s own files:

- `exemplar/web.cl` = the four `web/*` deftypes **only** (no platform import, no
  wrappers) — so the platform-load pre-resolve loads it cleanly.
- `exemplar/serve.cl` (new) = the `listen`/`accept`/`read`/`send` destructuring
  wrappers; it imports `[web [Listener Connection]]` + `[platform.web […]]`. It is
  NOT a sig-referenced module, so it is loaded only when `main.cl` imports it —
  **after** `(platform web)` — breaking the cycle.
- `exemplar/main.cl` imports `[serve [listen accept read send]]` + `[web [Request
  Response]]`. The "plumbing out of `main.cl`" intent (§3.5.3) is preserved — the
  plumbing is in `serve.cl`, just not in `web.cl`.

This is the minimal change that honors the design intent; it touches no interface
and no other crate. `/design` should update `poll-support.md §3.5.1/§3.5.3/§3.5.7`
to split the ADT module (sig-referenced, platform-import-free) from the wrapper
module (loaded after the platform), and record the `referenced_sig_modules`
pre-resolve as the governing constraint (so the next platform that wants
destructuring wrappers over its own ADTs follows the two-module pattern).

## Operational implication / Context

Any platform whose sigs reference `.cl` ADTs in module `M` makes `M` un-able to
import that platform. Wrappers that need the platform effects must live in a
**different** module than the ADTs `M`. This is a general platform-authoring
constraint, not a web-specific quirk — worth a one-line note wherever
`platform-interface.md §7.2` / the connection-handle pattern is documented.
