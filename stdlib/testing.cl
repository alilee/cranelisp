;; testing.cl — Test infrastructure group
;;
;; Submodules:
;;   testing.assertions — assert-eq, assert-true, assert-false, check
;;   testing.runner     — in-language test runner over discover-tests pairs
;;                        (run-one/run-all/run-matching/report/tally), the
;;                        Outcome/Tally ADTs and the discover-here sugar macro

(import [prelude []])

(mod assertions)
(mod runner)
