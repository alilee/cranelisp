# design/platform/archive/

Frozen historical platform design records. Superseded by current work, kept for
provenance only. **Not the target architecture** — nothing here is an
instruction, and where one of these documents contradicts a live record in
`design/platform/`, the live record wins.

Current design lives in `platform.md`, `platform-dlls.md`,
`poll-leaf-authoring.md` and `adt-marker-binding.md`.

| File | Sprint | What it documented | Why archived |
|---|---|---|---|
| `platform-registry-removal.md` | S57 (G8) + S58 addendum | The deletion of `PlatformRegistry` from int, and the cache-restore path that replaced it (DLL re-resolve from persisted platform declarations). | Work landed; `PlatformRegistry` is deleted and cache restore is operational. Lessons folded into the decision register, `platform.md` and `platform-dlls.md`. |
| `implementation-slice-s66.md` | S66 | A per-slice delta table, ordering, effort estimate and cross-crate dependency list for one sprint's platform work. | A sprint implementation plan whose work has landed. It describes a pre-S71 crate shape. |
| `sprint71-redesign.md` | S71 | The Phase-A boundary redesign: the schema format, the parser, the marker-type pattern, the `CLAdt` surface, the `HostCallbacks` growth to `alloc_with_tag` + `validate_schema`, the `ABI_VERSION` policy and the macro arm grammar. | Substantially superseded. `validate_schema` was removed at S76 (the layout-hash gate replaced it); the schema *declaration* dialect it defines was retired when platforms stopped declaring ADTs; the macro grammar and `ABI_VERSION` policy have moved on. Its durable content — the artifact grammar's rationale and the bump-rule shape — is carried by `platform.md` §4 and the source rustdoc. |
| `host-wiring-s76.md` | S76 | The W-Integrate host-wiring plan: a completeness audit of the round-trip path, a cross-crate seam map keyed to then-open filings, and a completion sequence. | The wiring landed; every seam it tracks is closed. It is a plan, not a contract. |
| `poll-support-s96.md` | S96 | The `poll_support` scaffolds, the web/stdio poll adoption, and the v8 leading-pair `(token, capacity)` carrier, plus a two-macro convergence skeleton and a `/dev` implementation order. | Three separate supersessions: the single-ABI cutover deleted the second macro; the **v9 ctx-vtable cutover deleted the leading-pair carrier entirely** (`(token, capacity)` is no longer a value, an operand or a node slot — the leaf acquires through the ctx vtable); and its implementation order has landed. Its live successor is `poll-leaf-authoring.md`. **Citation hazard:** this document cites "FIXME 0463" four times meaning a long-resolved question about the poll injection point. That number was later allocated to an unrelated `/examples` filing about a network lesson. Do not read either against the other. |
