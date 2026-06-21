;; default.cl — Default trait
;;
;; The Default trait provides a "zero value" for types. Types with a
;; natural empty/identity value implement this trait.
;;
;; Spec: plan-stdlib.md §3.3

(import [prelude []])

(import [primitives [Int Float Bool String]])
(import [fn.option [Option None]])

(deftrait Default
  (default [] self))

(impl Default Int
  (defn default [] 0))

(impl Default Float
  (defn default [] 0.0))

(impl Default Bool
  (defn default [] false))

(impl Default String
  (defn default [] ""))

;; ── Self-tests — DEFERRED (compiler limitation, S87 Stage C.2) ─────────
;; A `(mod test …)` for Default is NOT shipped this sprint because the only
;; way to exercise an impl is to CALL `(default)`, and a nullary,
;; return-type-polymorphic trait method does not reach codegen even with a
;; `:Type` annotation at the call site: `:Int (default)` typechecks but fails
;; with `codegen error … undefined function: default`. (Verified S87: the
;; call fails identically in a bare REPL, so this is a language limitation,
;; not a stdlib bug.) A `(mod test)` that fails CODEGEN would poison the whole
;; prelude load graph (not just its own run), so it is held until the
;; nullary-trait-method dispatch is implemented.
;;
;; DEFECT HANDOFF (per CLAUDE.md §Usability Findings and Defects): routed to
;; /qa for a narrow failing-not-ignored repro → /typecheck/backend. Minimal
;; shape: `(deftrait T (z [] self)) (impl T Int (defn z [] 0)) (:Int (z))`
;; ⇒ `undefined function: z` at codegen. See plan-stdlib.md §26.4.
