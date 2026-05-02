# Cranelisp — Architecture Overview

**Newcomer entry point.** Read this end-to-end first. Other documents elaborate; this one establishes the vocabulary the rest of the architecture uses.

## The language and the system

Cranelisp is a statically typed, pure-functional Lisp with type inference, trait-based dispatch, and Cranelift-backed JIT compilation. It is REPL-first: definitions accumulate during a session, redefinition is cheap, and JIT-emitted code is reclaimed when superseded. A persistent on-disk cache makes module loads incremental across sessions. A `--link` mode produces a standalone executable that depends only on the runtime and any platform DLLs the program calls.

The project is one Rust workspace of seven crates. Six of them are *surfaces* — bounded contexts the development triad (`/design`, `/dev`, `/review`) narrow-deploys to one at a time. The seventh, `cranelisp-types`, is owned by `/arch` and is the single home for everything that crosses crate boundaries. The full per-surface bounded contexts live in `bounded-contexts.md`; this overview introduces them in the order a reader meets them.

## How source becomes execution

A linear story first; concurrency next.

The **frontend** turns source text into an AST. It reads source bytes into S-expressions, expands macros, and builds a tree of structured nodes. The frontend is purely structural: every form downstream of it is a value defined in `cranelisp-types`, regardless of whether it originated from a file, the REPL, or another macro.

**Typecheck** infers types over that AST. It writes results in two places: directly back onto AST nodes — each node carries its inferred type and resolution choices — and into a per-module *symbol table*, the single store for a module's compilation state. The symbol table is the typecheck product. There is no separate "check result" passed alongside it.

The **backend** translates symbol-table entries into Cranelift IR and produces compilation artefacts: in-memory machine code for direct execution, object files for linking, and a cache pair (metadata plus object) for re-use across sessions. There is one compilation entry point regardless of mode; "in-memory vs object" is a property of the Cranelift module supplied to it, not a parameter on the entry point.

The **runtime** is what a running cranelisp program needs to execute: a heap, reference counting, drop glue, string and vector primitives, an IO trampoline that interprets effect chains, fork-join evaluation cells. JIT-emitted code calls into the runtime through a stable C-ABI surface. The runtime knows nothing about compilation, the REPL, or development tooling. That separation is load-bearing — it means a deployed `--link` executable does not pay for compiler infrastructure it never uses.

The **platform** crate is the shared interface contract between the cranelisp host and platform DLLs (the language's `IO` effect implementations). Both sides link against it; that is its purpose. Platform DLLs publish manifests describing the functions they expose; the host loads them and the IO trampoline dispatches through them.

The **integration layer** — the binary crate `src/`, paired with `cranelisp-exe-bundle` for the `--link` artefact — wires the other surfaces together. It owns the pipeline that turns a CLI argument or a REPL prompt into compiled, executing code. It owns development tooling: slash commands, tracing, observability, introspection. It is the only crate that knows the concrete carrier of compiled code (the abstraction is a marker trait in `cranelisp-types`; the concrete type lives here).

That is the linear story. Source enters frontend; frontend produces AST; typecheck annotates and populates the symbol table; backend emits code; runtime executes it; integration orchestrates.

## Where concurrency lives

The linear story is correct as a description of *what happens to one form*. It is wrong as a description of *what happens in time*. Real compilation is concurrent: multiple modules typecheck in parallel; macro expansion blocks waiting for callable code; object files are produced in the background while in-memory code is already running. And the system is interactive: the REPL is reading user input, the watcher is receiving file-change events from the OS, and a running program is doing its own thing. These are different problems with different invariants. The architecture treats them separately.

**Cadences** are how the system organizes execution in time. A cadence is a coherent pattern of work — what drives it, how it loops, who it talks to. The system has four:

- **Compilation cadence** lives inside the integration layer. Workers consume *work packets* off internal queues, process them, publish results, and notify a scheduler. Closed-loop within the compilation subsystem; no external clock.
- **REPL cadence** lives inside the integration layer. Turn-based, synchronous to user input. One prompt → one parse → one submission to the compilation cadence → wait → display.
- **Watcher cadence** lives inside the integration layer. Open-loop — its timing is dictated by the operating system. File-change events arrive on a callback thread and are captured into a channel, polled by the REPL at prompt boundaries to avoid mid-input interleave.
- **Runtime cadence** lives inside the runtime crate, executing as part of the running program. Atomic reference counting interleaved with normal execution; fork-join scopes during parallel evaluation. Invisible outside the running program — it produces no handoffs to the other cadences.

**Handoffs** are the typed values that cross cadence boundaries. The REPL submits an evaluation request to compilation and waits; compilation returns a result or an error; the watcher's events become re-register requests at prompt boundaries. The integration layer's facade pins the handoff types; the bounded context fixes the patterns (who initiates, who waits, who polls).

**Windows** are how a cadence accesses shared state. Each cadence holds typed handles to its own slice of state — compilation-cadence handles into compiler-shared state, REPL-cadence handles into session state, watcher-cadence handles into watcher state. There is no ambient session-state god-handle that any consumer can reach into. This means REPL changes cannot accidentally perturb worker behaviour and vice versa; the access containment IS the concurrency containment.

The vocabulary — *surface*, *bounded context*, *cadence*, *handoff*, *window* — is what makes the architecture navigable. Every per-surface design doc, every facade spec, every cross-crate decision uses these terms.

## The cross-crate types crate

`cranelisp-types` is the single home for everything that crosses crate boundaries. It depends on nothing else in the workspace, and nothing is allowed to invert that direction. The crate hosts two kinds of contract:

- **Value types** — the AST, types, sexp, symbol tables, errors, identifier newtypes, layout constants. These flow across the workspace by ownership.
- **Marker traits** for cross-crate generic shapes. Downstream crates implement these to supply concrete types where the boundary is generic; the concrete types live in the owning crate, never here. This is what keeps `cranelisp-types` ignorant of backend and runtime concrete state — the integration layer's compiled-code carrier is the canonical example.

The crate is `/arch`'s own; consumers file `target: /arch` to add or change shapes. The narrative companion to the types crate is `interfaces.md`, which describes each boundary type's purpose.

## Where to read next

- **Per-surface depth** → `bounded-contexts.md` — what each crate is responsible for, why the boundary is there, what crosses it
- **Architectural principles** → `principles.md` — the criteria every design decision is held against
- **As-designed public API** → `facades/{crate}.md` — one spec per surface; the integration-layer facade additionally enumerates cadences, handoffs, and windows
- **Cross-crate types** → `interfaces.md` — narrative companion to `cranelisp-types`
- **Language definition** → `spec/`
- **Per-crate design** → `design/{crate}/{crate}.md` (per-surface implementation direction; one per surface)
