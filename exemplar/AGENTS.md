# exemplar/

The Sudoku Solver exemplar is a real multi-module Cranelisp program that shows
the language working end to end. It is owned by `dev`, narrow-deployed to this
surface. Its design, design decisions and open obligations are in
[the exemplar design](plan-exemplar.md); this memory holds entry guidance.

- `exemplar/` and `src/main.rs` are the only trees that may depend on
  `stdlib/` (root [Design Principles](../AGENTS.md#design-principles),
  "Stdlib separation").
- Root [Testing](../AGENTS.md#testing) places the stdio and test-capture
  platforms under `qa` as test-suite dependencies. The exemplar reuses them
  and owns neither. The `web` platform in `platforms/web/` is the exemplar's
  own.

## Layout

| Path | Contents |
|---|---|
| `grid.cl`, `solver.cl`, `html.cl`, `form.cl` | The pure core; see [architecture](plan-exemplar.md#architecture) |
| `user.cl` | Headline stdio entry: form body → grid → solve → ASCII board, plus the rendered HTML page's size |
| `smoke.cl` | Quick smoke-test entry that solves and prints a fixed puzzle |
| `tests.cl` | Free-standing runner; exit code = number of passing tests |
| `main.cl`, `serve.cl`, `web.cl` | Web server entry, serve-loop wrappers, `web` platform types |
| `platforms/web/` | The `web` platform DLL (Rust) |

## Run

Run from the repository root. The platform DLLs build into `target/debug`,
which is not a default platform search directory, so set
`CRANELISP_PLATFORM_PATH`:

```bash
export CRANELISP_PLATFORM_PATH=target/debug CRANELISP_LIB=stdlib
cargo run -- --run exemplar/user.cl       # headline showcase, exit 0
cargo run -- --run exemplar/smoke.cl      # solves a fixed puzzle, exit 0
cargo run -- --run exemplar/tests.cl      # exit code 43 when all pass
CRANELISP_NO_LENIENT=1 cargo run -- --run exemplar/tests.cl   # serial; also 43
cargo run -- --run exemplar/main.cl       # serves HTTP until killed
```

- A green `tests.cl` run exits 43 (15 grid, 7 solver, 12 html, 9 form).
  Getting 43 under both the default parallel mode and
  `CRANELISP_NO_LENIENT=1` is the parallel ≡ serial guard.
  `solver/test-solve-parallel-equiv` pins a puzzle that requires
  backtracking.
- `solver/test-hard-puzzle` is deliberately excluded from the runner; see
  [copy-per-guess performance](plan-exemplar.md#copy-per-guess-performance).
- Before `--link`, build the workspace coherently: run `cargo build`, then
  `tests/scripts/build-link-prereqs.sh`. A partly stale build produces spurious
  `undefined reference to cranelisp_platform::…` link errors. That is build
  skew, not a compiler defect.

## Evidence

| Claim | Test |
|---|---|
| Web server serves the form, a valid solution and a 404, under `--run` and as a linked binary | `tests/exemplar_web.rs` |
| Concurrent `/slow` requests overlap instead of serialising (`--run`) | `tests/exemplar_web.rs::exemplar_web_server_fans_out_concurrent_requests_overlap` |
| `tests.cl` passes in the parallel and serial modes (`--run`) | `tests/exemplar.rs::s124_exemplar_tests_runner_lenient`, `::s124_exemplar_tests_runner_serial` |
| Linked `user.cl` output matches `--run` byte for byte | `tests/exemplar_link_run_parity.rs` |
| A warm serial `smoke.cl` run releases everything it allocates, with a zero-work control | `tests/exemplar_ownership_residue_s116.rs` |

State only what these tests show:

- Linked fan-out has not been established.
- The residue subject fails: it retains 2 blocks, carried as defect ACT-1018
  ([register](../tests/plan/s124-evidence-delta.md#1415-defects-carried-by-failing-tests)).
  Its zero-work control passes.
- The residue test covers `smoke.cl` only, not every exemplar entry.

## Known Issues

- **Do not run a REPL with `exemplar/` as the working directory.** The REPL
  `user` module adopts `./user.cl` as its backing file and shares the `user` <!-- doc-check: literal reason="REPL backing file in the working directory, not a tracked file" -->
  cache slot. It can rewrite the headline entry and poison the cache. Use a
  scratch directory with copies of the modules.
- **Do not add a file under `exemplar/` at a library module's path** (for
  example `collections/vec/test.cl`). The compiler loads it in place of that <!-- doc-check: literal reason="example of a forbidden path, not a tracked file" -->
  library module's declared child: defect ACT-1096, carried on failing tests
  ([register](../tests/plan/s124-evidence-delta.md#1415-defects-carried-by-failing-tests)).
- **Hard-puzzle backtracking is quadratic.** This is performance, not
  correctness: see
  [copy-per-guess performance](plan-exemplar.md#copy-per-guess-performance)
  (performance backlog 0408).
- **Do not change exemplar source to route around a compiler defect.** File the
  defect ([design decisions](plan-exemplar.md#design-decisions)).

## Conventions

- Use the prelude trait operators (`+ - * / = != < <= >`) for arithmetic and
  comparison. Access Vecs through `count`/`get`/`assoc`/`conj` imported from
  `collections.vec`. Import string primitives and `not` by name from
  `primitives`.
- Test functions are top-level `test-*` `defn`s returning `(Option String)`,
  where `None` means pass (`repl/spec/16-test-discovery.md` §16.1). Add each new
  test to `tests.cl` and its expected count. `cranelisp --test exemplar/main.cl`
  discovers every `test-*` function, so a listing that differs from the runner's
  shows a test the runner omits.
- Every batch `main` returns `(IO _)`; the inner Int is the process exit code.
- Only an entry (`smoke.cl`, `user.cl`, `tests.cl`, `main.cl`) declares a
  platform; the pure-core and helper modules import `platform.<name>` from the
  entry's declaration (`spec/10-io.md` §10.9.1).
- A runtime panic ends the process, the web server included, so request
  handling has no fault recovery. Code that a request's input can reach must
  not panic: use total or checked operations, bound every `get` and divisor,
  and render bad input as a response value
  ([web server](plan-exemplar.md#web-server)).
