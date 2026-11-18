---
id: ACT-1085
title: Two cranelisp processes on one project directory share its cache with no exclusion, so a later cached launch can run an object that does not match its metadata or its source
status: open
priority: required
from: qa
to: qa
sprint: 124
filed_at: 2026-11-18
refers_to:
  - design/int/int.md
  - src/cache.rs
  - src/session_v4/nice_worker.rs
  - tests/plan/s124-evidence-delta.md
---

## Request

Carry the hazard on record until the user decides whether its control is
built in S124, and hold its evidence allocation until then.

## The hazard

[Int §7.7](../../design/int/int.md#77-one-generation-beside-an-entry-act-1083),
*One cache owner per project directory*, states it. `design`(int) found it
in the review of ACT-1083's correction (`f2317af0`).

- A REPL, `--run`, `--link` and a `--test` child each open
  `{project_root}/.cranelisp-cache` with no exclusion between processes.
- Each process writes a module's `.meta`, then its `.o`, then records its
  manifest entry, and writes the manifest whole when its object work ends.
- Two user-launched processes can interleave those steps. One process's
  `.meta` can stand beside the other's `.o`, and the last manifest written
  replaces the other process's entries.
- **Face:** a later cached launch runs code that differs from its source.
  `--no-cache` is unaffected.
- **Reach:** an open REPL beside `--run`, `--link` or `--test` in another
  terminal, on one project.
- **Entered:** before S124. S124 did not introduce it and did not change
  its reach.

## Status of the claim

**Asserted with a named falsifier; not reproduced.**

- **Falsifier, from the design:** two concurrent sessions on one project,
  followed by a warm run, give a result that differs from `--no-cache`.
- **`qa`'s one probe is not evidence either way.** 400 loaded runs at
  `79a8c94c` of a REPL session and a `--run` on one directory, then a warm
  run, all gave the `--no-cache` result. The probe's REPL leg did not move
  a slot: with the importer loaded, the redefinition it issued was refused.
  No interleaving that mixes two generations was constructed.
- **Related, in the backend:** `dev` reports that the backend's private
  atomic write uses one fixed temporary name per target, so two processes
  writing one `.meta` or the manifest share a temporary. It matters only
  between processes.

## Proposed control

A session takes an exclusive advisory lock on the project's cache
directory without waiting; a session that does not get it uses a private
cache directory for its life (int §7.7). It is designed and not built. The
design states no change to any command's result.

## Decision needed

The user decides whether the lock is built in S124 or the hazard is
carried. No role has scheduled it.

## Evidence allocation, held

Held until the control is scheduled and its design is final.

- **`dev`(`src/`), module tier:** the *Owner* rows int §7.7 names. With one
  session alive on a root, a second session on that root uses a private
  directory and leaves the project's cache files byte for byte as they
  were; the row turns RED when the lock is removed. Negative: after the
  first session ends, a new session uses the project's cache.
- **`test`, one e2e cell (T-OWNER),** stated in the
  [evidence delta §14.3](../../tests/plan/s124-evidence-delta.md#143-returned-to-test).
- **Not allocated:** a cell for the falsifier itself. A mixed generation
  needs a particular interleaving of two processes, which no fixture
  built from user commands selects.

## Completion evidence

The user's decision is recorded. If the control is built: the module rows
and T-OWNER pass, each observed RED without the lock, and `qa` judges
adequacy and deletes this action. If it is carried: this action is marked
deferred with the decision, and the hazard is stated in the sprint record.

## What a reproduction takes (qa, 2026-11-19)

Judged constructible with a harness primitive the suite lacks, and not
attempted. The sequence, what it would show and what it would not are in
the [evidence delta §14.1](../../tests/plan/s124-evidence-delta.md#141-the-failing-set-by-owning-module),
*ACT-1085: what a reproduction takes*. Under *reproduce first* the hazard
has no committed reproduction; `sprint` schedules or declines one.
