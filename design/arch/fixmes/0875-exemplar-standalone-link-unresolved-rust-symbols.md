---
number: 0875
target: /qa
filed_by: /sprint
filed_at: 2026-07-25
sprint_filed: 118
refers_to: sprints/archive/sprint-117.md §Outcome "Deferred";
  exemplar/
status: open
---

# Exemplar standalone Link parity unverifiable — platform archive has unresolved Rust symbols

S117 Phase 6b could not verify the exemplar's standalone `--link` parity:
producing the executable fails **before** link-parity comparison because the
platform archive carries unresolved Rust symbols. The S117 close record parked
this in a deferral bullet with no FIXME; this file makes it durable.

No attribution exists yet — the visible error (unresolved symbols at archive
link time) may belong to exe-bundle, platform, or the build of the platform
staticlib itself. Per root `CLAUDE.md` §Cross-skill defect handoff, a minimal
repro is required before any cross-skill fix dispatch: `/qa` attributes (or
routes to `/testing` for reduction) and the repro — not the symptom — names
the owner.

Scheduling: S118 if adjacent to Track B's linked-startup work (0745 touches
the same link path); otherwise S119 with rationale.

## HEAD reproduction check — SYMPTOM DOES NOT REPRODUCE (`/port`, S118 Phase 6a)

One bounded attempt at HEAD `501e701f`, per the S118 P6 dispatch (confirm the
symptom, do not chase the fix).

Procedure — the documented precondition first (`exemplar/CLAUDE.md` §Known
Issues: a piecemeal build yields spurious `undefined reference to
cranelisp_platform::…`, which is build skew, not this defect): `cargo build`
then `bash tests/scripts/build-link-prereqs.sh`. Then a fresh scratch directory
containing only copies of `exemplar/*.cl`, **no cache present** (the
`.cranelisp-cache/` was created by this run), and:

```
CRANELISP_PLATFORM_PATH=<root>/target/debug CRANELISP_LIB=<root>/stdlib \
  <root>/target/debug/cranelisp --link user.cl
```

Result: **exit 0, executable produced.** The entire stderr is one line — the
`cc …` command echo; no unresolved symbols, no warnings. Running the produced
binary (`CRANELISP_PLATFORM_PATH` set) exits 0 and its stdout is **byte-identical
(659 bytes) to `--run user.cl`** from both cold and warm cache. Standalone Link
parity for the headline entry is therefore re-established at HEAD.

What this does and does not settle:

- It does **not** identify a fix. No attribution was ever dispatched, and
  nothing in S118 was aimed at this. The likeliest reading is that the S117
  environment carried a skewed platform-archive build state; the S118 W4
  link-path work (0745 result-owner, the linked-stub `ireduce` divergence
  closed at I5) also touched this path.
- It does mean there is currently **no observable symptom to attribute**. A
  `/qa` attribution dispatch at S119 would be attributing a symptom nobody can
  reproduce, which is the shape METHOD §3.3's verify-against-source rule exists
  to prevent.

Recommended disposition (`/qa`'s to make, not `/port`'s): close this FIXME as
not-reproducible-at-HEAD, and — if the parity claim is worth guarding — route
`/testing` a standing exemplar `--link`-then-run parity cell instead, which is
what would actually catch a recurrence. `/port` re-verifies at the next Phase-6
regardless.
