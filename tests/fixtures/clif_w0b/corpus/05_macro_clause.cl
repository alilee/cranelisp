;; W0.b lenient-class corpus 05 — non-concretized MACRO-CLAUSE body.
;; A `defmacro` clause is compiled to `__macro_twice_clause_0`. Macros expand
;; before typecheck, so a clause body carries no typecheck `codegen_view` and is
;; built by the LENIENT view builder (the "non-concretized macro-clause body"
;; reach, design §5 finding 1). Defining + using the macro forces the
;; `user::__macro_twice_clause_0` frame. Free-standing (primitives only); green
;; by construction.
(import [primitives [*]])

(defmacro twice [x] `(add-i64 ~x ~x))

(defn main []
  (Pure (twice 5)))
