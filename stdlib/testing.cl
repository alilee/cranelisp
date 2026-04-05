;; testing.cl — Test infrastructure group
;;
;; Submodules:
;;   testing.assertions — assert-eq, assert-true, assert-false
;;   testing.runner     — check macro, run-tests helpers

(import [prelude []])

(mod assertions)
(mod runner)
