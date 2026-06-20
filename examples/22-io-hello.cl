;; 22-io-hello.cl -- Testable IO with the test-capture platform
;;
;; Example 21 introduced the IO model (Pure, bind, combinators) and used
;; the `stdio` platform to write to the console. This example does NOT
;; re-teach those primitives -- it introduces ONE new idea: a *different
;; platform* that captures `print` output in memory instead of writing it
;; to the terminal.
;;
;; A "platform" supplies the concrete implementation of effectful
;; functions like `print`. The IO model is platform-agnostic: the same
;; `(print ...)` call means "write a string" regardless of where the
;; bytes actually go. Swapping `(platform stdio)` for
;; `(platform test-capture)` redirects every `print` into an in-memory
;; buffer -- which is exactly what you want when running a program under
;; test, where interactive console IO is unavailable or undesirable.
;;
;; This is the same separation the test suite relies on: examples 21-24
;; run unattended in CI, so an IO example that needs a human to read the
;; console would be unverifiable. test-capture makes IO programs
;; deterministic and self-checking.
;;
;; Running:
;;   ./target/debug/cranelisp --run examples/22-io-hello.cl
;;   (examples/lib/platforms/ ships host-correct symlinks for the
;;    test-capture DLL, so no environment variable is required.)

;; Load the test-capture platform DLL instead of stdio. `print` now
;; writes into an in-memory buffer rather than the console.
(platform test-capture)

;; The IO constructors are unchanged -- only the platform differs.
(import [primitives [Pure bind]])
(import [platform.test-capture [print]])


;; === Capturing a single effect ===

;; Under test-capture, `print` still has type (Fn [String] (IO Int)) and
;; still returns 0. The difference is purely in *where* the bytes go.
(defn test-captured-hello []
  ;; Effect: appends "hello, world" to the capture buffer (not the console).
  (print "hello, world"))                            ;; -> 0


;; === Sequencing captured effects ===

;; bind sequences captured prints exactly as it does console prints --
;; the platform swap is invisible to the IO plumbing.
(defn test-captured-sequence []
  ;; Effects: appends "hello," then "world!" to the capture buffer.
  (bind (print "hello,")
    (fn [_] (print "world!"))))                       ;; -> 0


;; === Mixing captured IO with a computed result ===

;; A program can perform captured effects and still thread a pure value
;; out through the IO chain. This is the shape every testable IO program
;; takes: do some effects, then report a checkable result.
(defn test-effect-then-result []
  ;; Effect: captures "computing...". Result: 99.
  (bind (print "computing...")
    (fn [_] (Pure 99))))                              ;; -> 99


;; --- Expected results ---
;;
;; test-captured-hello:     0
;; test-captured-sequence:  0
;; test-effect-then-result: 99
;;
;; Total: 0 + 0 + 99 = 99
;;
;; Captured output (in execution order, held in memory -- not printed):
;;   hello, world
;;   hello,
;;   world!
;;   computing...

(defn main []
  (bind (test-captured-hello) (fn [r1]
  (bind (test-captured-sequence) (fn [r2]
  (bind (test-effect-then-result) (fn [r3]
    (Pure (add-i64 r1 (add-i64 r2 r3)))
  )))))))
