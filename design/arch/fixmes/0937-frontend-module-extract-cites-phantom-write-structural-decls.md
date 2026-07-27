---
number: 0937
target: /dev
filed_by: /arch
filed_at: 2026-07-27
sprint_filed: 119
refers_to: crates/cranelisp-frontend/src/module_extract.rs:47
status: open
---

# `module_extract.rs` rustdoc cites the phantom `SymbolTable::write_structural_decls`

## Issue

FIXME 0918 (resolved S119) established that `SymbolTable::write_structural_decls`
never existed anywhere in the tree, and resolved the Decision-39 append-carrier
question by DELETING the unused `append_structural_decl` + `StructuralDeclEntry`
carrier: **the `pub` structural Vec fields on `SymbolTable` are the append
contract** (direct push, source/authorship order, no dedup).

One stale mention survives outside `/arch`'s edit boundary:
`crates/cranelisp-frontend/src/module_extract.rs:47` still cites
`write_structural_decls` as the bulk-load API.

## Proposed resolution

One-line rustdoc correction in the next `/dev`(frontend) change-set (or the
S120 wash's frontend touch): the structural Vec fields are the contract; there
is no bulk-load method. Delete this FIXME when the line is corrected.
