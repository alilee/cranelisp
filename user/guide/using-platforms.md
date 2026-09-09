# Using a platform — bringing `print`, `read-line`, and friends into scope

The core language has no built-in I/O. To `print`, read a line, open a socket, or
touch anything outside your program, you use a **platform** — a small native library
that supplies those effectful functions. The built-in `stdio` platform provides the
console operations most programs start with.

Using a platform is **two steps**, and missing the second is the usual first stumble:

```clojure
(platform stdio)                 ; step 1 — load the DLL and register its module
(import [platform.stdio [*]])    ; step 2 — bring its functions into scope

(defn main [] (print "hello world"))
```

If you only want to **use** a platform, this page is for you. To **write** a platform
of your own (in Rust), see [`writing-platforms.md`](writing-platforms.md) instead —
that is the author's side and none of it is needed to consume a platform.

## Step 1 — `(platform <name>)` loads and registers

```clojure
(platform stdio)
```

This resolves `stdio` to a DLL on the platform search path, loads it, and **registers
a synthetic module** named `platform.stdio` holding the functions the library exports
(`print`, `read-line`, …).

What it does **not** do: it does **not** bring those functions into your module's
scope. After `(platform stdio)` alone, writing `(print "hi")` fails with
`undefined variable: print` — the functions exist, in the `platform.stdio` module, but
nothing is imported yet. This is the common trap. `(platform <name>)` makes the module
*available*; it does not import from it, exactly like declaring a `mod` does not import
its names.

## Step 2 — `(import [platform.<name> [*]])` brings functions into scope

```clojure
(import [platform.stdio [*]])          ; everything the platform exports
;; or name what you use:
(import [platform.stdio [print read-line]])
```

Now `print` and `read-line` are bare names you can call. Import `[*]` for everything,
or list the specific functions — the same `import` form you use for any module.

## The module name is `platform.<name>` — **singular**

The synthetic module a platform registers is `platform.<name>` — **singular
`platform`**, with the platform's own name after the dot:

| Platform declared | Module to import from |
|---|---|
| `(platform stdio)` | `platform.stdio` |
| `(platform web)` | `platform.web` |
| `(platform my-io)` | `platform.my-io` |

A very easy typo is `platforms.stdio` (plural). There is **no** `platforms.stdio`
module, so `(import [platforms.stdio [*]])` fails with:

```
module 'platforms.stdio' not found
```

If you see that error, it is almost always the plural `s` — change `platforms` to
`platform` (singular). The pattern `platform.<name>` is normative in
[`spec/08-modules.md §8.9.3`](../../spec/08-modules.md).

REPL and `--run` behave identically here: without the import, both report
`undefined variable: print`; add the import and both work.

## A minimal working example

Put this in `hello.cl` and run it with `--run`:

```clojure
(platform stdio)
(import [platform.stdio [*]])

(defn main [] (print "hello world"))
```

```
$ cranelisp hello.cl --run
hello world
```

`main` must return an `IO` action; `print` does, so this is a well-formed IO program.
For the wider IO model (why effects have type `(IO a)`, how `main` is forced), see
[getting-started § Platforms and IO](../getting-started.md#platforms-and-io) and the
worked [`examples/21-hello-io.cl`](../../examples/21-hello-io.cl).

## Finding the DLL — the platform search path

`(platform stdio)` can only load the platform if the DLL is on the **platform search
path**. The `examples/` and `exemplar/` trees ship checked-in symlinks so `stdio`
resolves with no configuration. In your own project, add the directory holding the
built library — during development this is typically Cargo's output:

- set `CRANELISP_PLATFORM_PATH=target/debug` in the environment, **or**
- add `platform-dirs = ["target/debug"]` to your project's `Cranelisp.toml`.

Both are **additive** and follow the same union model as lib directories — see
[cli-reference § libraries](../cli-reference.md#where-cranelisp-looks-for-libraries-cranelisptoml)
and [`spec/08-modules.md §8.11.5`](../../spec/08-modules.md). If the DLL is not found
you get `platform 'stdio' not found` — that is a search-path problem (step-1 load),
distinct from the `undefined variable`/`module not found` scope problems above
(step 2).

## Checklist when `print` won't resolve

1. **`undefined variable: print`** → you declared `(platform stdio)` but did not
   `(import [platform.stdio [*]])`. Add step 2.
2. **`module 'platforms.stdio' not found`** → plural typo. It is `platform.stdio`
   (singular).
3. **`platform 'stdio' not found`** → the DLL is not on the search path. Set
   `CRANELISP_PLATFORM_PATH` or add `platform-dirs` (above).
