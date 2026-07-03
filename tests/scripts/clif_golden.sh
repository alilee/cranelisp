#!/usr/bin/env bash
# clif_golden.sh — L-B1 golden-CLIF capture + diff runner.
#
# Contract: tests/fixtures/clif_baseline/MANIFEST.md (capture pins) +
# tests/plan/s100-ownership-verification.md §3.1 (lane spec) +
# design/backend/ownership-codegen.md §13.1 (capture substrate, Hook H1).
#
# Usage:
#   tests/scripts/clif_golden.sh capture   # (re)capture goldens — B0-be and
#                                          # scoped re-baselines ONLY; never
#                                          # run casually (wholesale re-capture
#                                          # without attribution is forbidden)
#   tests/scripts/clif_golden.sh diff      # toggle-off dump of HEAD vs golden;
#                                          # exit non-zero on any delta
#   tests/scripts/clif_golden.sh selftest  # determinism self-test: double
#                                          # capture, byte-compare (H1 witness)
#
# Frames are extracted per `; === CLIF <module>::<symbol> ===` block and
# sorted by module::symbol (harness-side sort — the G-1 default resolution;
# if /backend's H1 work shows mid-function interleaving, the sort moves
# in-process and this script drops its own).
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
BIN="$ROOT/target/debug/cranelisp"
BASE="$ROOT/tests/fixtures/clif_baseline"
GOLD="$BASE/golden"
S99="$ROOT/tests/fixtures/s99"

# entry:source pairs — keep in sync with MANIFEST.md §Entries.
ENTRIES=(
  "01_adt_construct_match:$BASE/corpus/01_adt_construct_match.cl"
  "02_closures_fn_as_value:$BASE/corpus/02_closures_fn_as_value.cl"
  "03_auto_curry:$BASE/corpus/03_auto_curry.cl"
  "04_vec_cow_loop:$BASE/corpus/04_vec_cow_loop.cl"
  "05_string_externs:$BASE/corpus/05_string_externs.cl"
  "06_tco_loop:$BASE/corpus/06_tco_loop.cl"
  "07_trait_dispatch:$BASE/corpus/07_trait_dispatch.cl"
  "08_adt_in_vec_projection:$BASE/corpus/08_adt_in_vec_projection.cl"
  "09_parbind_launch:$BASE/corpus/09_parbind_launch.cl"
  "f1_machinery:$S99/f1_machinery.cl"
  "f2_contention:$S99/f2_contention.cl"
  "f3_inverted_search:$S99/f3_inverted_search.cl"
  "f4_sudoku:$S99/f4_sudoku.cl"
)

[ -x "$BIN" ] || { echo "error: $BIN not built (cargo build first)"; exit 2; }

# dump <source.cl> <out-file> — cold-cache `--run --no-cache` with the config
# pins (MANIFEST §Capture contract): emission-affecting env UNSET, fresh
# tmpdir, dump frames extracted from STDERR (the CRANELISP_CODEGEN_DUMP
# channel per design/backend/ownership-codegen.md §13.1 and backend lib.rs —
# stdout carries only the program's own output), sorted by module::symbol.
#
# `--no-cache` (Wave 3R, review F4): with the cache on, every symbol dumps
# TWICE — the JIT pass plus the nice-worker `.o` cache-write pass
# (`src/session_v4/nice_worker.rs::emit_object`; `dump_this` in backend
# lib.rs ignores `capture_clif: false`), and first-occurrence-=-JIT-pass
# relied only on the nice thread's OS priority (a race). `--no-cache`
# structurally eliminates the second pass: each symbol dumps exactly ONCE
# (the JIT pass — byte-identical to the committed goldens, verified 13/13
# at adoption), so a duplicate frame is a HARD ERROR (config drift), not
# something to dedup.
dump() {
  local src="$1" out="$2"
  local d
  d="$(mktemp -d)"
  cp "$src" "$d/user.cl"
  (
    cd "$d"
    # Emission-affecting pins (MANIFEST §Capture contract — keep in sync):
    #   NO_OWNERSHIP / NO_LENIENT / CAPTURE_BORROW / NONATOMIC_RC /
    #   RC_STATS / RC_DEC_CHECK (all gate CLIF emission in backend heap.rs /
    #   sparkability.rs) + NO_IO_SCHEDULE (pre-typecheck bind-chain
    #   transform, src/process_form.rs — shapes the ParBind entries).
    # Trace vars are cleared for stderr-channel hygiene: the dump frames
    # arrive on stderr, and compile-time trace lines could land mid-frame.
    env -u CRANELISP_NO_OWNERSHIP -u CRANELISP_NO_LENIENT \
        -u CRANELISP_CAPTURE_BORROW -u CRANELISP_NONATOMIC_RC \
        -u CRANELISP_RC_STATS -u CRANELISP_RC_DEC_CHECK \
        -u CRANELISP_NO_IO_SCHEDULE \
        -u CRANELISP_RC_TRACE -u CRANELISP_CODEGEN_TRACE \
        -u CRANELISP_GOT_TRACE -u CRANELISP_MODULE_TRACE \
        -u CRANELISP_SCHEDULER_TRACE -u CRANELISP_IO_TRACE \
        CRANELISP_CODEGEN_DUMP='*' "$BIN" --run user.cl --no-cache \
        >raw.txt 2>err.txt
  ) || true   # program exit code is its return value, not a failure signal
  # Extract frames (`; === CLIF <name> ===` ... `; === end CLIF <name> ===`)
  # and sort by the module::symbol header. Zero frames or a duplicate frame
  # is a hard error (review F3/F4 — the Wave-1 empty-vs-empty false green
  # and the cache-pass race, respectively).
  # NOTE (review F6): this extraction is mirrored in Rust in
  # tests/ownership_fences.rs::clif_golden_single_module_smoke — keep the
  # two in lockstep; a THIRD consumer is the bar for unifying them.
  python3 - "$d/err.txt" "$out" <<'PY'
import re, sys
raw = open(sys.argv[1]).read()
frames = {}
for m in re.finditer(r'; === CLIF (\S+) ===\n(.*?); === end CLIF \1 ===\n',
                     raw, re.S):
    name = m.group(1)
    if name in frames:
        sys.exit(f"DUPLICATE FRAME: {name} — under --no-cache each symbol "
                 "dumps exactly once (JIT pass); a second frame means the "
                 "nice-worker .o cache-write pass leaked into the capture "
                 "(config drift). Hard error — do NOT dedup.")
    frames[name] = m.group(0)
if not frames:
    sys.exit("NO FRAMES: zero CLIF frames extracted from the dump stream — "
             "the empty-vs-empty false-green class (S102 Wave 1). Check the "
             "stderr channel and CRANELISP_CODEGEN_DUMP wiring before "
             "trusting any diff.")
with open(sys.argv[2], 'w') as f:
    for name in sorted(frames):
        f.write(frames[name])
PY
  rm -rf "$d"
}

mode="${1:-diff}"
fail=0
case "$mode" in
  capture)
    mkdir -p "$GOLD"
    for e in "${ENTRIES[@]}"; do
      name="${e%%:*}"; src="${e#*:}"
      # Determinism self-test before writing the golden (MANIFEST pin).
      dump "$src" "$GOLD/.$name.a"; dump "$src" "$GOLD/.$name.b"
      if ! cmp -s "$GOLD/.$name.a" "$GOLD/.$name.b"; then
        echo "NONDETERMINISTIC: $name — H1 (frame-atomic/ordered dump) not satisfied; golden NOT written"
        rm -f "$GOLD/.$name.a" "$GOLD/.$name.b"; fail=1; continue
      fi
      mv "$GOLD/.$name.a" "$GOLD/$name.clif"; rm -f "$GOLD/.$name.b"
      echo "captured: $name ($(wc -l < "$GOLD/$name.clif") lines)"
    done
    ;;
  diff)
    for e in "${ENTRIES[@]}"; do
      name="${e%%:*}"; src="${e#*:}"
      if [ ! -f "$GOLD/$name.clif" ]; then
        echo "MISSING GOLDEN: $name (B0-be capture not landed?)"; fail=1; continue
      fi
      t="$(mktemp)"; dump "$src" "$t"
      if ! diff -u "$GOLD/$name.clif" "$t" > /dev/null; then
        echo "DIFF: $name"; diff -u "$GOLD/$name.clif" "$t" | head -40; fail=1
      else
        echo "ok: $name"
      fi
      rm -f "$t"
    done
    ;;
  selftest)
    for e in "${ENTRIES[@]}"; do
      name="${e%%:*}"; src="${e#*:}"
      a="$(mktemp)"; b="$(mktemp)"
      dump "$src" "$a"; dump "$src" "$b"
      if cmp -s "$a" "$b"; then echo "deterministic: $name"; else echo "NONDETERMINISTIC: $name"; fail=1; fi
      rm -f "$a" "$b"
    done
    ;;
  *) echo "usage: $0 {capture|diff|selftest}"; exit 2 ;;
esac
exit $fail
