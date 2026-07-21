;; core/syntax/test.cl — self-tests for core.syntax (module core.syntax.test)
;;
;; Separate backing file (extraction-stable per spec §8.2.5). Parent declares
;; `(mod- test)`.
;;
;; This module is the SList substrate every macro-authoring module in the stdlib
;; stands on — `derive.helpers`, `defs` and `derive` all fold and reverse through
;; `sfold`/`sreverse`. It had no self-tests before S115.
;;
;; ── WHAT IS NOT HERE, AND WHY (FIXME 0835) ────────────────────────────
;;
;; This file is DELIBERATELY THIN, and the missing tests are the point of this
;; note. `sreverse` and `slist` have NO cases below, and `sfold` has only its
;; base cases, because a `test-*` function that builds a **two-cell SList of
;; heap `Sexp`** aborts the compiler process when invoked through the test
;; runner:
;;
;;   (defn- slen [xs] :Int (sfold (fn [n _] (add-i64 n 1)) 0 xs))
;;   (defn test-x [] :(Option String)
;;     (assert-eq 2 (slen (SCons (SexpSym "a") (SCons (SexpSym "b") SNil)))))
;;   ⇒ "6 passed, 0 failed, 0 panicked"   then   corrupted double-linked list
;;
;; Note WHERE it dies: the assertions all pass and the tally prints. The abort
;; is in glibc, on teardown — this is a drop-glue/RC defect over nested heap
;; ADTs, not a logic error, and it is reached through `discover-tests`/`run-one`
;; (a ONE-cell list is fine, and the same fold run directly at the REPL is fine).
;; Filed as FIXME 0835 with this cell as the minimal repro.
;;
;; So the honest position is: `sempty?`, `sfold`'s base case, and `make-def-name`
;; are pinned below; `sreverse`, `slist`, and `sfold`'s inductive case are NOT
;; COVERED AT ALL and cannot be until 0835 closes. The drafted-and-removed cases
;; were: sreverse of empty / preserves length / puts last first / of a singleton
;; / twice-is-identity; slist empty / single / preserves order; sfold counts
;; elements / is left-associative. RESTORE THAT SET WHEN 0835 CLOSES — it is
;; written down here precisely so the gap is not re-discovered from scratch.

(import [super [sempty? sfold make-def-name]])
(import [testing.assertions [assert-eq assert-true assert-false]])
(import [macros [Sexp SList SCons SNil SexpSym SexpInt]])
(import [primitives [Option String Int Bool add-i64]])

;; ── sempty? ────────────────────────────────────────────────────────────

(defn test-sempty-on-nil [] :(Option String)
  ;; nothing constrains the element type of a bare `SNil`, so it needs the
  ;; annotation (spec §3.11).
  (assert-true (sempty? :(SList Sexp) SNil)))

(defn test-sempty-false-on-cons [] :(Option String)
  (assert-false (sempty? (SCons (SexpSym "a") SNil))))

;; ── sfold (base case only — see the header) ────────────────────────────

(defn test-sfold-over-empty-returns-init [] :(Option String)
  (assert-eq 99 (sfold (fn [acc _] (add-i64 acc 1)) 99 :(SList Sexp) SNil)))

;; ── make-def-name ──────────────────────────────────────────────────────
;; The mangling `defs.cl`'s `def`/`def-` depend on: symbol → symbol + "-def".

(defn test-make-def-name-appends-suffix [] :(Option String)
  (assert-eq "counter-def"
             (match (make-def-name (SexpSym "counter")) [(SexpSym s) s _ "<not-a-sym>"])))

(defn test-make-def-name-passes-non-symbols-through [] :(Option String)
  ;; a non-symbol sexp is returned unchanged, not mangled into one
  (assert-eq 7 (match (make-def-name (SexpInt 7)) [(SexpInt n) n _ -1])))
