;; text/display/test.cl — self-tests for text.display (module text.display.test)
;;
;; Separate backing file (extraction-stable per spec §8.2.5). Parent declares
;; `(mod test)`. HARNESS-FREE: `testing.assertions` depends on `text.display`
;; (assert-eq's `Display` bound), so importing the harness here forms a load
;; cycle. Tests return `(Option String)` directly via inline `if` over `str-eq`.

(import [super [Display show]])
(import [primitives [Option Some None String str-eq]])

(defn test-show-int [] :(Option String)
  (if (str-eq "42" (show 42)) None (Some "show 42")))

(defn test-show-bool [] :(Option String)
  (if (str-eq "true" (show true)) None (Some "show true")))

(defn test-show-string [] :(Option String)
  (if (str-eq "hi" (show "hi")) None (Some "show hi")))
