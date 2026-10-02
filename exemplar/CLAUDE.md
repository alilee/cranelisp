# exemplar/

The Sudoku Solver exemplar is a real multi-module Cranelisp program that shows
the language working end to end. It is owned by `dev`, narrow-deployed to this
surface. Its design, design decisions and open obligations are in
[the exemplar design](plan-exemplar.md); this memory holds entry guidance.

- `exemplar/` and `src/main.rs` are the only trees that may depend on
  `stdlib/` (root [Design Principles](../CLAUDE.md#design-principles),
  "Stdlib separation").
- Root [Testing](../CLAUDE.md#testing) places the stdio and test-capture
  platforms under `qa` as test-suite dependencies. The exemplar reuses them
  and owns neither. The `web` platform in `platforms/web/` is the exemplar's
  own.

## Layout

| Path | Contents |
|---|---|
| `grid.cl`, `solver.cl`, `html.cl`, `form.cl` | The pure core; see [architecture](plan-exemplar.md#architecture) |
| `user.cl` | Headline stdio entry: form body → grid → solve → ASCII board, plus the rendered HTML page's size |
| `solver.cl` `main` | Quick smoke test that solves and prints a fixed puzzle |
| `tests.cl` | Free-standing runner; exit code = number of passing tests |
| `main.cl`, `serve.cl`, `web.cl` | Web server entry, serve-loop wrappers, `web` platform types |
| `platforms/web/` | The `web` platform DLL (Rust) |
| `collections/`, `compare/`, `fn/`, `num/`, `text/` | Copies of stdlib module `test.cl` files; not part of the showcase or its runner |

## Run

Run from the repository root. The platform DLLs build into `target/debug`,
which is not a default platform search directory, so set
`CRANELISP_PLATFORM_PATH`:

```bash
export CRANELISP_PLATFORM_PATH=target/debug CRANELISP_LIB=stdlib
cargo run -- --run exemplar/user.cl       # headline showcase, exit 0
cargo run -- --run exemplar/tests.cl      # exit code 40 when all pass
CRANELISP_NO_LENIENT=1 cargo run -- --run exemplar/tests.cl   # serial; also 40
cargo run -- --run exemplar/main.cl       # serves HTTP until killed
```

- A green `tests.cl` run exits 40 (15 grid, 7 solver, 10 html, 8 form).
  Getting 40 under both the default parallel mode and
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
| Linked `user.cl` output matches `--run` byte for byte | `tests/exemplar_link_run_parity.rs` |
| Heap residue of a warm serial `solver.cl` run stays within a bound, with a zero-work control | `tests/exemplar_ownership_residue_s116.rs` |

State only what these tests show:

- Linked fan-out has not been established.
- The residue test checks a bound. It does not show that every exemplar entry
  balances exactly.

## Known Issues

- **Do not run a REPL with `exemplar/` as the working directory.** The REPL
  `user` module adopts `./user.cl` as its backing file and shares the `user` <!-- doc-check: literal reason="REPL backing file in the working directory, not a tracked file" -->
  cache slot. It can rewrite the headline entry and poison the cache. Use a
  scratch directory with copies of the modules.
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
  test to `tests.cl` and its expected count. In-language discovery is
  REPL-only, so the runner calls tests directly.
- Every batch `main` returns `(IO _)`; the inner Int is the process exit code.
