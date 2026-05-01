---
number: 02
title: Narrow interfaces
---

# Principle 02 — Narrow interfaces

**Statement.** Boundary types should be the minimum surface area needed for the consuming crate's bounded context. Adding a field to a boundary type has O(n) impact across skills; adding an internal type has O(1) impact.

**Rationale.** The cost of a boundary field is paid by every consumer at every change, in perpetuity. Interface changes therefore require `/arch` review.

**Consequence.** Internal types stay `pub(crate)` by default (see `design/arch/facades/{crate}.md` — Public-API discipline). When something must cross a crate boundary, the question is "what is the minimum the consumer needs?" — not "what does the producer happen to have?"
