(mod numerics)
(import [primitives [*] macros [SNil SCons] numerics [+ > /]])

;; ── Trace ADT Accessors ──────────────────────────────────────────────────────
;; TraceCall has 5 fields: tname tparams tresult tchildren tnanos

(defn trace-name "Extract the function name from a Trace node." [t]
  (match t
    [(TraceCall name _ _ _ _) name]))

(defn trace-params "Extract formatted parameter strings from a Trace node as an SList." [t]
  (match t
    [(TraceCall _ params _ _ _) params]))

(defn trace-result "Extract the formatted result string from a Trace node." [t]
  (match t
    [(TraceCall _ _ result _ _) result]))

(defn trace-children "Extract child traces from a Trace node as an SList." [t]
  (match t
    [(TraceCall _ _ _ children _) children]))

(defn trace-nanos "Extract wall-clock nanoseconds from a Trace node." [t]
  (match t
    [(TraceCall _ _ _ _ nanos) nanos]))

;; ── Trace Tree Queries ───────────────────────────────────────────────────────

(defn trace-children-max-depth
  "Helper: find max depth across an SList of Trace nodes (self-recursive)."
  [xs acc]
  (match xs
    [SNil acc
     (SCons h tl)
       (let [d (+ 1 (trace-children-max-depth (trace-children h) 0))]
         (trace-children-max-depth tl (if (> d acc) d acc)))]))

(defn trace-depth "Maximum call depth of the trace tree (root = depth 1)." [t]
  (+ 1 (trace-children-max-depth (trace-children t) 0)))

(defn trace-children-flatten
  "Helper: flatten an SList of Trace nodes, prepending each node and its subtree to acc."
  [xs acc]
  (match xs
    [SNil acc
     (SCons h tl)
       (trace-children-flatten tl (SCons h (trace-children-flatten (trace-children h) acc)))]))

(defn trace-flatten "All Trace nodes in pre-order as an SList." [t]
  (SCons t (trace-children-flatten (trace-children t) SNil)))

;; ── Trace Display ─────────────────────────────────────────────────────────────

(defn trace-params-string
  "Build \" p1 p2 ...\" string from an SList of parameter strings."
  [ps]
  (match ps
    [SNil ""
     (SCons h tl) (str-concat " " (str-concat h (trace-params-string tl)))]))

(defn trace-call-string
  "Format a Trace node as a syntactically correct call: \"(name p1 p2 ...)\"."
  [t]
  (str-concat "("
    (str-concat (trace-name t)
      (str-concat (trace-params-string (trace-params t)) ")"))))

(defn trace-show
  "Format a single Trace node as \"(name p1 p2 ...) => result [Xms]\"."
  [t]
  (str-concat (trace-call-string t)
    (str-concat " => "
      (str-concat (trace-result t)
        (str-concat " ["
          (str-concat (int-to-string (/ (trace-nanos t) 1000000)) "ms]"))))))

(defn trace-show-children
  "Recursively format an SList of Trace nodes at a given indentation level.
   Each node is formatted as indent + call-string + newline, followed by its children indented further."
  [xs indent]
  (match xs
    [SNil ""
     (SCons h tl)
       (str-concat
         (str-concat indent
           (str-concat (trace-show h)
             (str-concat "\n"
               (trace-show-children (trace-children h) (str-concat indent "  ")))))
         (trace-show-children tl indent))]))

(defn trace-show-tree
  "Format a full trace tree as a multi-line string.
   Skips the synthetic root \"::trace::\" frame — shows only user function calls."
  [t]
  (trace-show-children (trace-children t) ""))
