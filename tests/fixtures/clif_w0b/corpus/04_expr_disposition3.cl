;; W0.b lenient-class corpus 04 — `__expr` (§3.11.2 disposition-3) body.
;; A top-level bare expression is wrapped as the synthetic `__expr` entry
;; (requires_codegen_view == false — lib.rs "REPL-`__expr`" arm), so its body is
;; built by the LENIENT view builder. Under `--run` the wrapper is codegen'd,
;; forcing `user::__expr` alongside the batch entry `main`.
;; Free-standing (primitives only).
(import [primitives [*]])

(primitives/pure (add-i64 1 2))

(defn main [] (primitives/pure 0))
