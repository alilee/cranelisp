;; text/display/test.cl — self-tests for text.display (module text.display.test)
;;
;; Separate backing file (extraction-stable per spec §8.2.5). Parent declares
;; `(mod- test)`. HARNESS-FREE: `testing.assertions` depends on `text.display`
;; (assert-eq's `Display` bound), so importing the harness here forms a load
;; cycle. Tests return `(Option String)` directly via inline `if` over `str-eq`.

(import [super [Display show]])
(import [primitives [Option Some None Result Ok Err Pair String Int str-eq str-concat]])

(defn test-show-int [] :(Option String)
  (if (str-eq "42" (show 42)) None (Some "show 42")))

(defn test-show-bool [] :(Option String)
  (if (str-eq "true" (show true)) None (Some "show true")))

(defn test-show-string [] :(Option String)
  (if (str-eq "hi" (show "hi")) None (Some "show hi")))

;; ── Option, Result, Pair ─────────────────────────────────────────────

(defn- shows [want got] :(Option String)
  (if (str-eq want got) None (Some (str-concat "expected " want))))

(defn test-show-some [] :(Option String)
  (shows "Some(42)" (show (Some 42))))

(defn test-show-none [] :(Option String)
  (shows "None" (show :(Option Int) None)))

(defn test-show-ok [] :(Option String)
  (shows "Ok(1)" (show :(Result Int String) (Ok 1))))

(defn test-show-err [] :(Option String)
  (shows "Err(bad)" (show :(Result Int String) (Err "bad"))))

(defn test-show-pair [] :(Option String)
  (shows "Pair(1 a)" (show (Pair 1 "a"))))

(defn test-show-nested [] :(Option String)
  (shows "Some(Pair(None true))" (show (Some (Pair :(Option Int) None true)))))

;; A nested payload shows by its own impl, so the constructor wraps it again.
(defn test-show-some-of-some [] :(Option String)
  (shows "Some(Some(1))" (show (Some (Some 1)))))
