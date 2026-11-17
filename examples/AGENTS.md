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
   Name sub-test helpers `check-`. A `test-` name makes a function a test
   under `--test`, which warns about every `test-` function that is not of
   type `(Fn [] (Option String))`; only 38 defines tests.
4. **Exit changes are coordinated.** Any added, removed or renamed example,
   and any deliberate exit change, needs `test` to reconcile
   `tests/examples.rs` in the same change-set. `training` does not edit
   `tests/`.
5. **Free-standing.** Examples MUST NOT depend on `stdlib/`, so the sequence
   validates the language rather than the library ([root separation rule](../AGENTS.md#design-principles)). Shared helpers belong in `lib/`, under the rules in
   [`lib/README.md`](lib/README.md).

## Verification

Build first, then run every entry — each top-level `NN-*.cl`,
`16-modules/main.cl` and `37-method-import/main.cl` — in four cells: cold and
warm cache × `--run` and `--link`-then-execute. Each must reach its documented
exit.

Run this Bash recipe from the repository root. It copies only the examples
project, clears inherited compiler settings, disables both environment files,
and keeps cache and REPL backing-file writes in its private scratch directory.
Compare every printed exit with `tests/examples.rs`; these are teaching-material
replays, not independent acceptance tests.

```bash
cargo build --bin cranelisp
bash tests/scripts/build-link-prereqs.sh
(
  repo=$PWD
  scratch=$(mktemp -d /tmp/cranelisp-training-XXXXXX)
  trap 'rm -rf "$scratch"' EXIT
  tar -C examples --exclude=.cranelisp-cache -cf - . | tar -C "$scratch" -xf -
  for name in ${!CRANELISP_@}; do unset "$name"; done
  export CRANELISP_NO_ENV=1 CRANELISP_AGENT_PROVIDER=
  export CRANELISP_PLATFORM_PATH="$repo/target/debug"
  cd "$scratch" || exit 1
  compiler="$repo/target/debug/cranelisp"
  for f in [0-9]*.cl 16-modules/main.cl 37-method-import/main.cl; do
    find . -type d -name .cranelisp-cache -prune -exec rm -rf {} +
    "$compiler" --run "$f" </dev/null >run.log 2>&1
    echo "$f cold run => $?"
    "$compiler" --run "$f" </dev/null >run.log 2>&1
    echo "$f warm run => $?"
    # --link rejects --no-cache; remove caches only in this private copy.
    find . -type d -name .cranelisp-cache -prune -exec rm -rf {} +
    for cell in cold warm; do
      if "$compiler" --link -o "$scratch/linked" "$f" >link.log 2>&1; then
        "$scratch/linked" </dev/null >run.log 2>&1
        echo "$f $cell link => $?"
      else
        echo "$f $cell link FAILED"; cat link.log
      fi
    done
  done
  "$compiler" --test 38-program-tests.cl </dev/null
)
```

- **Test mode:** 38 must report four `ok` lines and exit 0.
- **Free-standing lookup:** keep `CRANELISP_LIB` unset and
  `CRANELISP_NO_ENV=1`. Library directories are an additive union
  ([lib directory configuration](../spec/08-modules.md#8114-lib-directory-configuration-tested-testsspec_platformscranelisp_toml_lib_dirs_resolves_module));
  an inherited or file-supplied stdlib path breaks free-standing runs.
- **Diagnostics:** inspect `run.log` or `link.log` inside the subshell if a
  cell differs; its exit trap removes the scratch copy and logs on completion.
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

Here the [`training` contract's](../.agents/skills/training/SKILL.md#the-standing-question)
cadence is every increment, against the whole sequence rather than the delta.
Report the answer whether or not the brief asked, and keep
`plan-examples.md` §4 current with it.
