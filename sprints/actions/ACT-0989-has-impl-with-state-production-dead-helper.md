---
id: ACT-0989
title: Move the bare-name impl-existence predicates, including `has_impl_with_state`, out of production code into test support
status: open
priority: advisory
from: arch
to: dev
sprint: 122
filed_at: 2026-09-24
refers_to:
  - crates/cranelisp-typecheck/src/checker.rs
  - crates/cranelisp-typecheck/src/checker/test_support.rs
  - design/typecheck/typecheck.md
---

## Request

`design` (typecheck) decided the disposition on 2026-09-24; it is recorded in
`design/typecheck/typecheck.md` §9.1. Implement it in `cranelisp-typecheck`.

Verified at source 2026-09-24: production checks impl existence only through
`TypeCheckEnv::has_impl_in_home`. The four bare-name-rooted predicates in
`crates/cranelisp-typecheck/src/checker.rs` have no production caller:
`TypeCheckEnv::has_impl`, `TypeCheckEnv::has_impl_in_module`,
`ModuleReadView::has_impl` and `TypeCheckEnv::has_impl_with_state`. Their
callers are in `checker/tests.rs`, `checker/test_support.rs`
(`TestFixture::has_impl`), `builtins.rs` (test-only) and other unit tests. Two
`#[allow(dead_code)]` attributes keep them compiling. Comments in
`traits/dispatch.rs` and `traits/monomorphise.rs` record two wrong-rejects caused
by using the bare-name form in production.

- Make the predicates unavailable to production code. For example, compile them
  only under `#[cfg(test)]` or move them into the test support. Remove the
  `#[allow(dead_code)]` attributes they needed.
- Keep the chain-follow positive and negative cells in `checker/tests.rs` and
  the `TestFixture::has_impl` behavior that existing unit tests depend on.
- Repair the `checker.rs` rustdoc that presents `has_impl_with_state` as a
  production impl-discovery path.

This is private to the crate and does not change the public API.

## Completion evidence

- No non-test build of `cranelisp-typecheck` can call a bare-name-rooted
  impl-existence predicate.
- The chain-follow unit cells still pass.
