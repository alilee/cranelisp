---
id: ACT-0993
title: Establish safe host–DLL version alignment before manifest exchange
status: deferred
priority: required
from: sprint
to: arch
filed_at: 2026-09-27
refers_to:
  - src/platform.rs
  - crates/cranelisp-platform/src/lib.rs
  - design/arch/platform-interface.md
  - design/platform/platform.md
---

## Request

Design the platform DLL version-alignment protocol in a future sprint, with
`design` (platform). The user deferred this work on 2026-09-27 and prioritised
the reproduced REPL crash. This is PM-1 from the S122 QA intake; it remains a
release-relevant risk, not a claim of safe incompatible-DLL loading.

Verified against `src/platform.rs`: the host calls an entry point returning
`PlatformManifest` by value, then checks the returned `abi_version`.
The struct's layout is defined in `crates/cranelisp-platform/src/lib.rs`.
A newer DLL returning a larger manifest can exceed an older host's return
storage before that check. This risk is established by boundary reasoning;
no crashing incompatible-DLL example has been executed.

Establish compatibility before any call or data exchange that requires matching
layouts, including host callbacks. Assess version-specific entry points and a
stable bootstrap/query interface without treating either as approved. Cover
both the compiler loader and linked executable loader. Bring the exact public
API/ABI delta, transition policy and generated baseline changes to the user.

## Completion evidence

QA defines controlled mismatched host/DLL cases, including a newer, larger
manifest, and demonstrates rejection before incompatible layouts are used.
Compatible DLLs must still load and execute through the supported modes.
Resolve the unconditional mismatch-rejection claim in the standing platform
contract. Complete this work before promising safe version rejection for
independently distributed DLLs across changing manifest layouts.
