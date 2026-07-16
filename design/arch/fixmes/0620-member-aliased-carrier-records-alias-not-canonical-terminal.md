---
number: 0620
target: /arch
filed_by: /dev
filed_at: 2026-07-16
sprint_filed: 110
scheduled: S110
refers_to: crates/cranelisp-types/src/resolve.rs:458 + :687 (`Resolved.fq`
  composes `symbol: canonical_symbol(written_name)`); the producer recorder
  crates/cranelisp-typecheck/src/checker.rs::record_reference_target (→
  def_resolved → scope_resolve → ResolutionScope::resolve). Consumed by the
  S110 W1 backend keyed read (design/arch/backend-keyed-consumer.md §1.1 sum-ctor
  + field-accessor rows / §1.3 `entry_at`).
status: open
---

# The W1 keyed-consumer carrier records the bare-ALIAS FQ for member-canonical-keyed symbols (sum ctors + field accessors), not the canonical `Type.member` terminal — W1 (backend call seam) is BLOCKED

## One line

For every **member-canonical-keyed** symbol — every sum-type constructor and
every field accessor (S109 dotted-ctor keying: the real `Def` lives under
`member_key(Type, member)` and the bare name is an `Import` alias onto it) — the
`resolved_targets` carrier records the **bare-alias** `FQSymbol` (`{home, "Pure"}`,
`{home, "v"}`), NOT the **canonical terminal storage key** (`{home, "IO.Pure"}`,
`{home, "Box.v"}`) where `Resolved.entry` actually lives. W1's `entry_at`
(a DIRECT two-level map read, NO chain-follow — Rev-2 §1.3) therefore lands on the
`Import` alias entry and hard-misses. This is a producer non-conformance against
the §1.1 carrier contract (which says the sum-ctor / accessor carrier IS the
canonical `member_key`), and it **blocks the W1 call-seam flip**.

## Root cause (verified against source, this wave)

`cranelisp_types::resolve::Resolved.fq` (resolve.rs:458 and :687) is composed as

```rust
fq: FQSymbol { module: home.clone(), symbol: canonical_symbol(name) }
```

where `home` is the chain-follow TERMINUS (correct) but `symbol` is
`canonical_symbol(WRITTEN_NAME)` — a cleanup of the looked-up spelling (`/`-split,
non-empty-remainder guard), **not** the terminal entry's actual storage key. The
sibling field `Resolved.entry` IS the terminal (non-`Import`) `Def`, but its
symbol-table KEY is not surfaced. For a non-member-aliased symbol (user fn,
primitive) the written name == storage key, so the carrier is correct and W1's
other S-sites (S1/S2/S5/S6/S7/S8/S9) key-read correctly. For a member-aliased
symbol the written name (`v`, `Pure`) != storage key (`Box.v`, `IO.Pure`), so the
carrier is the alias.

The producer path for a bare construction ctor / accessor reference is
`infer_var` → `record_reference_target` → `def_resolved` → `scope_resolve` →
`ResolutionScope::resolve`, i.e. it records `Resolved.fq`. It does NOT go through
`instantiate_ctor` / `dotted_member_identity` (which DO derive the canonical
`member_key` — pattern position and the dotted `Type.member` spelling both key
correctly). The W0.1b completeness-sweep table
(`backend-keyed-consumer.md` §1.1.1, "Ctor construction/reference … `instantiate_ctor`
… correct") **mis-attributes the recorder**: bare construction/reference ctors and
all field-accessor refs are recorded by `record_reference_target`, not
`instantiate_ctor`, and that recorder emits the alias.

## Scope (BROAD — verified empirically)

- Bare sum-ctor construction `(Pure x)`, `(Just n)` — same-module user `deftype`
  AND imported/seeded alike (`src/bootstrap.rs:256` + typecheck `register_constructors`
  both install the bare name as an `Import` alias onto the canonical
  `member_key` `Def`).
- Bare field-accessor calls `(v box)`, `(px pt)` — accessors are UserFn `Def`s
  keyed `Type.field` with a bare `Import` alias.
- (W2, same root) bare ctor / accessor VALUE references (`None` as a value, an
  accessor as a fn-value) will hit the identical gap at the value seam.

Dispatch-leg **Apply** carriers (trait-method / sig-dispatch / auto-curry via
`dispatch_target_fq` → `resolved_call_to_fqsymbol` / the W0.1b `impl_module`) are
UNAFFECTED — they record the mangled entry's own storage key directly.

## Repro (member-aliased accessor; the exemplar of ~6 e2e classes)

```
(deftype (Box a) [:a v])
(defn h [] (v (Box 7)))   ; W1: "undefined function: v" — carrier {user, "v"} is the Import alias
```

`v`'s carrier is `{user, v}` (the alias); the real accessor `Def` lives at
`{user, "Box.v"}`. `entry_at({user, v})` reads the `Import` alias → no
`callable_got_slot`, not a ctor, not extern → falls through to the func-id tail →
`undefined function: v`.

## Requested resolution (the DECISION is /arch's — where the canonical key is sourced)

The §1.1 carrier for a member-aliased reference must be the **terminal storage
key** (`member_key(Type, member)` — where `Resolved.entry` lives), matching the
sum-ctor / accessor rows already written in the contract. Two candidate sites,
both cross-crate (why this is filed, not fixed — /dev was narrow-deployed to
`cranelisp-backend`):

1. **`cranelisp-types` (resolve.rs), /arch-owned — HIGH blast radius.** Make
   `Resolved.fq` carry the terminal storage key (the key `resolve_terminal_entry_and_home`
   terminated at) instead of `canonical_symbol(written_name)`. Ripples to EVERY
   `Resolved.fq` consumer (display, `callees`, the §8.6.4 conflict gate, harvest,
   …) — must be assessed for byte-identity of the display/`/search` surfaces and
   the S20/S21 pins before adopting.
2. **`cranelisp-typecheck` (record_reference_target), typecheck-owned — LOW blast
   radius.** Derive the canonical storage key for the CARRIER only (the
   `resolved_targets` insert is unread until W1), mirroring `instantiate_ctor` /
   `dotted_member_identity`'s canonical-key derivation off the terminal entry.
   Leaves `Resolved.fq` (and all its other consumers) untouched.

`/arch` rules the site; a `/dev` (typecheck or types) change-set lands it with a
per-leg unit pin (member-aliased ctor carrier == canonical `member_key`;
member-aliased accessor carrier == canonical `member_key`). No cache/schema bump
(the carrier fields already ride schema-19; this only changes the VALUE recorded,
which is unread pre-W1). After it lands, W1's `entry_at` keyed read resolves the
canonical `Def` for every ctor/accessor site, the S3/S4 ctor arm can flip to the
keyed `ctor_meta_at` read (currently on the untouched legacy resolver — Rev-2
§1.2 option b), and the ~6 e2e accessor/ctor classes + `stdlib_conformance` go
green.

## Why W1 could not just chain-follow in the backend (Rev-2 §1.3)

`entry_at` is defined as a direct read with NO import-chain walk, NO alias
substitution — a bounded "follow the one `Import` edge on the fetched key" would
be exactly the resolver the initiative deletes (the P8 half-resolver Rev-2
forbids), so it is not an option. The producer must record the terminal key.
