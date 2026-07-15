;; W0.b lenient-class corpus 04 — `__expr` (§3.11.2 disposition-3) body.
;; A top-level bare expression is wrapped as the synthetic `__expr` entry
;; (requires_codegen_view == false — lib.rs "REPL-`__expr`" arm), so its body is
;; built by the LENIENT view builder. Under `--run` the wrapper is codegen'd,
;; forcing the sole `user::__expr` frame. Free-standing (primitives only); green
;; by construction. NOTE: no `main` — the top-level expression IS the compiled
;; unit here; that is precisely what makes it the `__expr` class.
(import [primitives [*]])

(Pure (add-i64 1 2))
