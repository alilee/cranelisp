---
number: 0010
title: Base-pointer ABI
status: operative
---

# 0010 — Base-pointer ABI

heap pointers point to the start of the allocation (offset 0 = alloc_size, offset 8 = rc, offset 16+ = payload). Positive offsets throughout. Departing from the sketch's interior-pointer convention.
