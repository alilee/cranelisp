;; testing.cl — Test infrastructure group
;;
;; Submodules:
;;   testing.assertions — assert-eq, assert-true, assert-false
;;   testing.runner     — in-language test runner over discover-tests pairs
;;                        (run-one/run-all/run-matching/report/tally), the
;;                        Outcome/Tally ADTs, the discover-here sugar macro,
;;                        and the check macro

(import [prelude []])

(mod assertions)
(mod runner)
