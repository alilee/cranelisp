;; core/trace.cl — Trace display functions
;;
;; Re-exports the compiler-seeded Trace ADT from `primitives` and provides
;; human-readable display functions for trace trees.
;;
;; Users import the combined package:
;;   (import [core.trace [*]])
;; brings in the re-exported primitives and the display functions together.
;;
;; Spec: 03-types.md §3.2.4, 11-stdlib.md §11.5

;; Re-export trace primitives so users get everything from one import
(import [prelude []])

;; `trace` is a root special form (no import needed); only the Trace ADT + its
;; accessors are re-exported from `primitives` (FIXME 0266, user ruling 2026-06-04).
(export [primitives [Trace TraceCall name params result children nanos]])

;; Import what we need for our own definitions
(import [primitives [*]])
(import [macros [SCons SNil]])

;; ── Single-Node Display ─────────────────────────────────────────────────────

(defn trace-call-string
  "Format a Trace node as a call signature: \"(name p1 p2 ...)\"."
  [t]
  (match t
    [(TraceCall n p _ _ _)
      (str-concat "(" (str-concat n (str-concat " " (str-concat (format-params p) ")"))))]))

(defn format-params
  "Format an SList of param strings as space-separated text."
  [ps]
  (match ps
    [(SCons head tail)
       (match tail
         [(SCons _ _) (str-concat head (str-concat " " (format-params tail)))
          SNil         head])
     SNil ""]))

(defn trace-show
  "Format a single Trace node as \"(name p1 ...) => result [Xms]\"."
  [t]
  (match t
    [(TraceCall n p r _ ns)
      (str-concat (trace-call-string t)
        (str-concat " => "
          (str-concat r
            (str-concat " ["
              (str-concat (int-to-string (div-i64 ns 1000000)) "ms]")))))]))

;; ── Tree Display ────────────────────────────────────────────────────────────

(defn trace-show-node
  "Format a Trace node with indentation, then recurse into children."
  [t indent]
  (match t
    [(TraceCall n p r ch ns)
      (let [line (str-concat indent (trace-show t))]
        (str-concat line (str-concat "\n" (trace-show-children ch (str-concat indent "  ")))))]))

(defn trace-show-children
  "Format an SList of child Trace nodes with indentation."
  [ch indent]
  (match ch
    [(SCons head tail)
       (str-concat (trace-show-node head indent) (trace-show-children tail indent))
     SNil ""]))

(defn trace-show-tree
  "Format a trace tree as a multi-line string.
   Skips the root ::trace:: frame and shows its children directly."
  [t]
  (match t
    [(TraceCall n _ _ ch _)
      (if (str-eq n "::trace::")
        (trace-show-children ch "")
        (trace-show-node t ""))]))
