;; defs/test.cl — self-tests for stdlib definition macros (module defs.test)

(import [super [const def]])
(import [testing.assertions [assert-eq]])
(import [primitives [Option String]])

(const cached-constant 7)
(def cached-value 42)

(defn test-const-value [] :(Option String)
  (assert-eq 7 cached-constant))

(defn test-def-value [] :(Option String)
  (assert-eq 42 cached-value))
