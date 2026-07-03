#!/usr/bin/env bash
# run_fences_checked.sh — the fence corpus under a checking allocator (the
# ASan-lane fallback on this aarch64 toolchain). See README.md; contract:
# tests/plan/s100-ownership-verification.md §3.2 (two-condition rule) + §3.4.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../../.." && pwd)"
BIN="${CRANELISP_ASAN_BINARY:-$ROOT/target/debug/cranelisp}"
[ -x "$BIN" ] || { echo "error: $BIN not built"; exit 2; }

# The fence shapes, mirrored from tests/ownership_fences.rs templates at
# their sustained N (keep in sync when fences change; the canonical file is
# the source of truth for expected VALUES — this lane asserts survival under
# the checking allocator, i.e. no abort, exit code stable across two runs).
run_shape() {
  local name="$1" src="$2"
  local d; d="$(mktemp -d)"
  printf '%s' "$src" > "$d/user.cl"
  local codes=()
  for _ in 1 2; do
    ( cd "$d" && MALLOC_CHECK_=3 MALLOC_PERTURB_=42 "$BIN" --run user.cl \
        >/dev/null 2>"$d/err.txt" ); codes+=("$?")
  done
  if [ "${codes[0]}" != "${codes[1]}" ] || grep -qiE "malloc|abort|corrupt" "$d/err.txt"; then
    echo "FAIL: $name (exits ${codes[0]}/${codes[1]})"; cat "$d/err.txt" | head -5
    rm -rf "$d"; return 1
  fi
  echo "ok: $name (exit ${codes[0]})"
  rm -rf "$d"
}

fail=0
run_shape s1_borrowed_param '(import [primitives [*]])
(defn use-len [:String s] (str-len s))
(defn spin [:Int n :Int acc :String s]
  (if (eq-i64 n 0) acc
    (spin (sub-i64 n 1) (add-i64 acc (add-i64 (use-len s) (str-len s))) s)))
(defn main [] (Pure (spin 2000 0 "hello")))
' || fail=1
run_shape s2_projection_reads '(import [primitives [*]])
(defn walk [v :Int n :Int acc]
  (if (eq-i64 n 0) acc
    (walk v (sub-i64 n 1)
      (add-i64 acc (add-i64 (str-len (vec-get v 0)) (vec-len v))))))
(defn main [] (Pure (walk ["aa" "bbb"] 2000 0)))
' || fail=1
run_shape s3_temporaries '(import [primitives [*]])
(defn use-len [:String s] (str-len s))
(defn spin [:Int n :Int acc]
  (if (eq-i64 n 0) acc
    (spin (sub-i64 n 1) (add-i64 acc (use-len (str-concat "ab" "cd"))))))
(defn main [] (Pure (spin 2000 0)))
' || fail=1
run_shape l_c2a_tco_backedge '(import [primitives [*]])
(defn spin [:Int n :String s]
  (if (eq-i64 n 0) (str-len s)
    (spin (sub-i64 n 1) (substring (str-concat s "ab") 0 3))))
(defn main [] (Pure (spin 10000 "xy")))
' || fail=1
run_shape l_d3c_suspension_borrow '(import [primitives [*]])
(defn leaf [v :Int i] (str-len (vec-get v 0)))
(defn mid-of [:Int lo :Int hi] (add-i64 lo (div-i64 (sub-i64 hi lo) 2)))
(defn reduce-range [v :Int lo :Int hi]
  (if (eq-i64 (sub-i64 hi lo) 1) (leaf v lo)
    (let [m (mid-of lo hi)]
      (add-i64 (reduce-range v lo m) (reduce-range v m hi)))))
(defn main [] (Pure (reduce-range ["hello" "bb"] 0 256)))
' || fail=1
exit $fail
