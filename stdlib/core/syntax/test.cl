;; core/syntax/test.cl — self-tests for core.syntax (module core.syntax.test)
;;
;; Separate backing file (extraction-stable per spec §8.2.5). Parent declares
;; `(mod- test)`.
;;
;; This module is the SList substrate every macro-authoring module in the stdlib
;; stands on — `derive.helpers`, `defs` and `derive` all fold and reverse through
;; `sfold`/`sreverse`. It had no self-tests before S115.
;;
;; `sreverse`, `slist`, and sfold's inductive case remain uncovered. Restoring
;; their broader historical matrix is outside this focused self-test slice.

(import [super [sempty? sfold make-def-name annotated? annotation unannotate]])
(import [testing.assertions [assert-eq assert-true assert-false]])
(import [macros [Sexp SList SCons SNil SexpSym SexpInt SexpAnnotated]])
(import [primitives [Option Some None String Int Bool add-i64]])

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

;; ── Reader-annotation helpers ─────────────────────────────────────────

(defn test-annotated-recognises-reader-annotation [] :(Option String)
  (assert-true (annotated? (SexpAnnotated (SexpSym "Int") (SexpInt 7)))))

(defn test-annotated-rejects-ordinary-sexp [] :(Option String)
  (assert-false (annotated? (SexpInt 7))))

(defn test-annotation-projects-reader-annotation [] :(Option String)
  (match (annotation (SexpAnnotated (SexpSym "Int") (SexpInt 7)))
    [(Some ann) (assert-eq "Int" (match ann [(SexpSym name) name _ "<not-a-sym>"]))
     None (assert-true false)]))

(defn test-annotation-is-none-for-ordinary-sexp [] :(Option String)
  (match (annotation (SexpInt 7))
    [None (assert-true true)
     (Some _) (assert-true false)]))

(defn test-unannotate-projects-reader-subject [] :(Option String)
  (assert-eq 7
             (match (unannotate (SexpAnnotated (SexpSym "Int") (SexpInt 7)))
               [(SexpInt value) value
                _ -1])))

(defn test-unannotate-preserves-ordinary-sexp [] :(Option String)
  (assert-eq 7 (match (unannotate (SexpInt 7)) [(SexpInt value) value _ -1])))
