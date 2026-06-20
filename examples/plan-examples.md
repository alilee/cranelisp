# Examples Plan — Learning Sequence Design

**Skill**: `/examples`
**Rebaselined**: Sprint 86 (Phase 6b)

This document describes the learning sequence in `examples/` — what each
example teaches, the design principles that govern the sequence, and how to
keep every example runnable. It is the working reference for the `/examples`
skill; the authoritative inventory is the on-disk file set itself.

> **Ring framing retired.** Earlier revisions of this plan organised
> examples by "ring" (R0 core → R4 effects), the project-wide scheduling
> axis that was retired in Sprint 64. Rings no longer appear here. Each
> example is now described by the **language capability it teaches**, not by
> a ring number. Where ordering matters it is a pedagogical dependency
> ("uses closures from 12"), not a ring gate.

## 1. Design Principles

1. **One new capability per example.** Each example introduces exactly one
   language concept and is the simplest program that makes it clear.
2. **Cumulative.** An example may use any capability taught by an earlier
   example, and nothing else. The sequence reads as a deliberate arc.
3. **Free-standing — zero stdlib dependency.** Examples MUST NOT import
   `stdlib/`. They define helpers inline from compiler primitives and
   special forms, and resolve names through the tiny, standalone
   `examples/lib/prelude.cl` (configured via `examples/Cranelisp.toml`
   `lib-dirs = ["./lib"]`). This validates the *language*, not the library.
   This is a hard rule from the root `CLAUDE.md` §"Stdlib separation".
4. **Every example is runnable at all times.** A broken example teaches that
   the language is broken. Examples are sentinels: they catch real
   regressions by exercising the language end-to-end in compact form.
5. **Verifiable via exit code.** Every example defines `main` returning an
   Int (wrapped in `Pure`/`IO` where the IO model is in play). The return
   value is the sum of sub-test pass counts (1 per passing sub-test). A
   non-zero, *expected* exit code means every sub-test passed; a drop below
   the expected total signals a regression. The e2e guard
   `tests/examples.rs` pins each file's expected exit code.
6. **Comments explain the capability**, not the syntax — the code and its
   results teach the syntax.

## 2. The Learning Sequence (current on-disk set)

30 top-level `.cl` files plus the `16-modules/` multi-file project. Each row
is the **capability taught**. Exit code is the documented `main` return
(sum of sub-test passes); it is the value `tests/examples.rs` asserts.

| # | File | Capability taught | Exit |
|---|------|-------------------|------|
| 01 | `01-integers.cl` | Integer literals and the four arithmetic operators | 69 |
| 02 | `02-booleans.cl` | Boolean literals and comparison operators | 5 |
| 03 | `03-let-bindings.cl` | Local names with `let`; sequential and nested bindings | 97 |
| 04 | `04-functions.cl` | Named functions with `defn`; `if` as an expression | 135 |
| 05 | `05-recursion.cl` | Self-recursion and tail-call optimisation | 111 |
| 06 | `06-enums.cl` | Nullary ADTs (`deftype` enums) and `match` | 104 |
| 07 | `07-polymorphism.cl` | Let-polymorphism and type variables | 119 |
| 08 | `08-floats.cl` | Float literals and the monomorphic `*-f64` primitives | 10 |
| 09 | `09-strings.cl` | The `String` type and string operations | 55 |
| 10 | `10-adts.cl` | Product and sum types with typed fields | 9 |
| 11 | `11-destructuring.cl` | Pattern matching that binds constructor fields | 69 |
| 12 | `12-closures.cl` | Anonymous functions (`fn`) and variable capture | 7 |
| 13 | `13-higher-order.cl` | Functions as arguments and return values; composition | 203 |
| 14 | `14-vecs.cl` | `Vec` literals and operations | 29 |
| 15 | `15-traits.cl` | Trait-based operator dispatch (`Num`/`Eq`/`Ord`) + constrained polymorphism | 58 |
| 16 | `16-modules/` | Multi-file programs: `mod`, `import`, `export`, `defn-` | 47 |
| 17 | `17-display.cl` | User-defined traits and the `Display` trait | 176 |
| 18 | `18-macros.cl` | `defmacro`, quasiquote/unquote, multi-clause macros | 89 |
| 19 | `19-threading.cl` | Data pipelines with `->`, `->>` and friends | 130 |
| 20 | `20-adt-traits.cl` | Implementing traits (`Eq`, `Display`) for user ADTs | 39 |
| 21 | `21-hello-io.cl` | The IO model: `Pure`, `bind`, combinators, platform IO | 243 |
| 22 | `22-io-hello.cl` | Testable IO via the `test-capture` platform | 99 |
| 23 | `23-io-sequence.cl` | IO sequencing patterns with explicit `bind` chains | 178 |
| 24 | `24-io-echo.cl` | Input with `read-line`; read-then-process | 20 |
| 25 | `25-curry.cl` | Multi-signature dispatch and auto-currying | 118 |
| 26 | `26-functor.cl` | The `Functor` trait (higher-kinded `fmap`) | 91 |
| 27 | `27-lazy-seq.cl` | Lazy sequences (`take`, `filter`, `iterate`) | 183 |
| 28 | `28-parallel.cl` | Parallel evaluation (`par-let`, `bind!`) | 67 |
| 29 | `29-annotations.cl` | The `:Type` annotation model (capstone) | 119 |
| 30 | `30-parallel-map-reduce.cl` | Self-parallelising Vec map-reduce via divide-and-conquer `let` | 56 |

### Notes on specific entries

- **08-floats** — every sub-test asserts a *true* proposition (each correct
  result contributes 1), so a regression in any float op or comparison
  lowers the exit code below the expected total. (An earlier revision had a
  `test-ge` constructed to return 0 on success — a `1+…+0+…` total of 9 —
  which inverted the regression signal. Rewritten in S86 so the pass=1
  invariant holds uniformly; exit code moved 9 → 10.)
- **21 vs 22** — 21 is the full IO-model introduction (`Pure`, `bind`,
  combinators, recursion, then real `stdio` side effects). 22 deliberately
  does **not** re-teach those primitives; its single new idea is the
  *test-capture platform* — a platform that captures `print` output in
  memory, which is how the IO examples stay verifiable in CI. (S86 trimmed
  22 from a near-duplicate of 21's first parts down to this distinct
  content; exit code moved 11 → 99.)
- **29-annotations** — positioned as a **capstone**, not a feature
  introduction. `:Type` has appeared since example 03 (defn params), 10
  (deftype fields), and in every REPL result line; 29 names the single
  unifying model (`:Type` binds the immediately-following form and unifies
  its inferred type) that all those appearances share.

## 3. Platform / IO examples (21–24) — running without an env var

The IO examples load a platform DLL (`stdio` or `test-capture`). The
resolver (`src/platform.rs`) selects the host-native extension at compile
time (`.so` on Linux, `.dylib` on macOS, `.dll` on Windows) and searches:

1. `{project_root}/platforms/` — i.e. `examples/platforms/`
2. `{lib_dir}/platforms/` for each `lib-dirs` entry
3. directories in `CRANELISP_PLATFORM_PATH`

`examples/lib/platforms/` ships **host-correct symlinks for each platform**
— `stdio.so` / `test-capture.so` (Linux) and `stdio.dylib` /
`test-capture.dylib` (macOS) — each pointing at cargo's built
`target/debug/libcranelisp_{stdio,test_capture}.{so,dylib}`. Because
`Cranelisp.toml` puts `./lib` on `lib-dirs`, the resolver finds these via
**Tier 2** (`{lib_dir}/platforms/`), and because it looks for the native
extension first, the matching symlink resolves — so the IO examples run with
no environment variable:

```bash
./target/debug/cranelisp --run examples/21-hello-io.cl
```

> **Why `examples/lib/platforms/` and not `examples/platforms/`.**
> `examples/platforms/` is `.gitignore`d (`.gitignore:21`), so symlinks
> placed there cannot be committed — that is why the original macOS-only
> `.dylib` symlinks there were never in the repo, and why the IO examples
> failed on a fresh Linux checkout. `examples/lib/` is tracked, so the
> committable fix lives under `examples/lib/platforms/` and reaches the
> resolver via the existing `lib-dirs = ["./lib"]` (Tier 2). NOTE: a global
> `*.dylib` ignore (`.gitignore:22`) still prevents committing the macOS
> `.dylib` symlinks — only the `.so` symlinks are tracked. macOS users (or
> any host lacking a checked-in symlink) set the search path explicitly:
> `CRANELISP_PLATFORM_PATH=target/debug`.

> **Resolver note (S86).** No resolver change was needed: extension
> selection (`src/platform.rs`) is already host-correct, and
> `libcranelisp_{name}.{ext}` is already a recognised candidate. The
> residual wart — a checkout must carry one symlink per host, and the global
> `*.dylib` ignore blocks committing the macOS variant — was judged marginal
> and NOT worth a `/platform` FIXME: the `.so` symlinks resolve the
> reference (Linux) host, and macOS retains the documented env-var path.

## 4. Spec feature coverage

Every major language feature in the spec is exercised by at least one
example. (Spec sections track the current `spec/` numbering; verify against
the spec when annotating coverage.)

| Feature area | Example(s) |
|---|---|
| Literals (Int, Float, Bool) | 01, 02, 08 |
| `let` bindings | 03 |
| `if` expressions | 04 |
| Named functions (`defn`) | 04 |
| Recursion + TCO | 05 |
| ADTs (enums, products, sums, polymorphic) | 06, 10 |
| Pattern matching | 06, 11 |
| Let-polymorphism | 07 |
| Strings | 09 |
| Closures / lambdas / capture | 12 |
| Higher-order functions, composition | 13 |
| Vec | 14 |
| Traits + operator dispatch + constrained poly | 15, 17, 20 |
| Modules / imports / exports | 16 |
| Macros (defmacro, quasiquote, multi-clause) | 18 |
| Threading macros | 19 |
| Multi-signature dispatch + auto-currying | 25 |
| Higher-kinded traits (Functor) | 26 |
| Lazy sequences | 27 |
| IO model (`Pure`, `bind`, platform IO, `read-line`) | 21, 22, 23, 24 |
| Parallel evaluation (`par-let`, lenient eval) | 28, 30 |
| `:Type` annotation model | 29 |

## 5. Verification

At the start and end of every sprint, run every example and confirm the
documented exit code:

```bash
for f in examples/[0-9]*.cl; do
  ./target/debug/cranelisp --run "$f" >/dev/null 2>&1; echo "$f => $?"
done
./target/debug/cranelisp --run examples/16-modules/main.cl
```

A zero exit (or a value below the documented total) means a sub-test failed
— investigate before shipping. The e2e guard `tests/examples.rs` (owned by
`/qa`) enforces the on-disk file set against an expected-exit table; any
file add/remove/rename, or any deliberate exit-code change, requires `/qa`
to reconcile that table.

## Next skills

- `/qa` — reconcile the `tests/examples.rs` expected-exit table for the S86
  changes (08-floats 9→10, 22-io-hello 11→99); replay `tests/examples.rs`.
- `/docs` — getting-started can lead with `01-integers` and reference the
  platform-symlink note here for the IO examples.
