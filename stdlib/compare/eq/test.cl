;; compare/eq/test.cl — self-tests for compare.eq (module compare.eq.test)
;;
;; Authored as a SEPARATE backing file (not an inline `(mod test …)` body) so
;; the compiler's one-time inline-submodule EXTRACTION (spec §8.2.5) cannot
;; strip it: an inline body is extracted to this path on first compile and the
;; parent left with a bare `(mod test)`; authoring the file directly is the
;; durable, extraction-stable form. The parent declares `(mod test)`.
;;
;; HARNESS-FREE: `testing.assertions` depends on `compare.eq` (its `assert-eq`
;; carries an `Eq` bound), so importing the harness here would form a load
;; cycle. Tests return `(Option String)` directly via inline `if` — None = pass.

(import [super [Eq = !=]])
(import [primitives [Option Some None String Bool]])

(defn test-int-eq [] :(Option String)
  (if (= 1 1) None (Some "expected (= 1 1) true")))

(defn test-int-neq [] :(Option String)
  (if (= 1 2) (Some "expected (= 1 2) false") None))

(defn test-int-bang-eq [] :(Option String)
  (if (!= 1 2) None (Some "expected (!= 1 2) true")))

(defn test-bool-eq [] :(Option String)
  (if (= true true) None (Some "expected (= true true) true")))

(defn test-string-eq [] :(Option String)
  (if (= "a" "a") None (Some "expected string eq true")))

(defn test-string-bang-eq [] :(Option String)
  (if (!= "a" "b") None (Some "expected string neq true")))
