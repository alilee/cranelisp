# examples/ — the learning sequence

Owned by `training`. The sequence is the product, not the individual programs:
each one introduces what a reader cannot yet do, rests on what precedes it, and
earns its place. [`plan-examples.md`](plan-examples.md) records what each
example teaches, the design rules and the open gaps. The numbered files and
directory projects on disk are the sequence of record.

## Every example runs, always

**A broken example is worse than an absent one** — it teaches a reader that the
language is broken, and a reader cannot tell which of the two of you is wrong.

1. **Only teach what exists.** Write examples for delivered behaviour, never for
   planned behaviour. If a feature does not run in batch mode yet, its example
   does not exist yet.
2. **Verify the whole sequence every sprint**, at open and at close, not only
   the files that changed. Zero broken examples is a hard gate. A compiler
   change that breaks an example is a suspected defect routed to `qa`, not a
   reason to quietly drop the example.
3. **Self-verifying `main`.** Every example defines `main` returning
   `(Pure <Int>)`. The documented exit — the low byte of that Int — is pinned
   in `tests/examples.rs` (owned by `test`). Any other exit, including 0, is a
   failure. The target form sums one pass per sub-test. Many existing examples
   still sum values instead, a gap recorded in `plan-examples.md` §4.4.
4. **Exit changes are coordinated.** Any added, removed or renamed example,
   and any deliberate exit change, needs `test` to reconcile
   `tests/examples.rs` in the same change-set. `training` does not edit
   `tests/`.
5. **Free-standing.** Examples MUST NOT depend on `stdlib/`, so the sequence
   validates the language rather than the library ([root separation rule](../CLAUDE.md#design-principles)). Shared helpers belong in `lib/`, under the rules in
   [`lib/README.md`](lib/README.md).

## Verification

Build first, then run every entry — each top-level `NN-*.cl`,
`16-modules/main.cl` and `37-method-import/main.cl` — in four cells: cold and
warm cache × `--run` and `--link`-then-execute. Each must reach its documented
exit.

```bash
cargo build
bash tests/scripts/build-link-prereqs.sh          # platform libraries --link resolves from target/debug
export CRANELISP_PLATFORM_PATH=$PWD/target/debug  # 34 needs async-demo, which has no link in lib/platforms
EX="examples/[0-9]*.cl examples/16-modules/main.cl examples/37-method-import/main.cl"
for f in $EX; do ./target/debug/cranelisp --run "$f" >/dev/null 2>&1; echo "$f => $?"; done
for f in $EX; do o=target/ex-$(echo $f | tr / _); \
  ./target/debug/cranelisp --link "$f" -o "$o" >/dev/null 2>&1 && "$o" >/dev/null 2>&1; \
  echo "$f => $?"; done
```

- **Cold cells:** add `--no-cache` to the run loop. `--link` rejects
  `--no-cache` (`user/cli-reference.md`), so for cold link cells remove
  `examples/.cranelisp-cache/` first.
- **Never set `CRANELISP_LIB`.** Library directories are an additive union
  ([lib directory configuration](../spec/08-modules.md#8114-lib-directory-configuration-tested-testsspec_platformscranelisp_toml_lib_dirs_resolves_module)), so it adds the real stdlib and breaks free-standing runs.
- **Platform links.** `lib/platforms/` holds committed `stdio.so` and
  `test-capture.so` links. On a host without matching links, set
  `CRANELISP_PLATFORM_PATH`.
- **Missing prerequisites look like compiler failures.** Without the
  prerequisite script, platform-linking examples fail inside `cc` with
  undefined `std` symbols. Without the platform path, 34 reports
  `platform 'async-demo' not found`.

If a compiler change broke an example, file the suspected defect and either
move the example away from the broken feature or withdraw it until the feature
works. Record which you did, and why, in the report.

## The standing question

The `training` contract asks it against the whole sequence every increment, not
against the delta: coverage (what is unteachable from the sequence today?),
order, nuance (does it teach boundaries, traps and negative space?), and
readability as reading material. Answer it whether or not the brief asked, and
keep `plan-examples.md` §4 current with the answer.
