;; 21-hello-io.cl -- Introduction to the IO model
;;
;; IO is an opaque built-in type: an (IO a) value describes a deferred
;; computation that yields an a. Evaluation never performs an effect.
;; Calling a function, including print, returns a value without performing
;; IO. Effects occur only when the runtime executes an IO value.
;;
;; This example introduces the public operations step by step:
;;
;;   1. pure   -- lift a value into IO without adding an effect
;;   2. bind   -- sequence IO actions, passing results to continuations
;;   3. Conditional IO -- both branches return the same IO type
;;   4. Helper combinators built from pure and bind
;;   5. Helper functions that return IO
;;   6. Recursive composition of IO actions
;;   7. Platform IO -- console output, and reusing an IO value
;;
;; When main returns (IO a), the runtime executes that computation and
;; obtains its result. Returning (pure 42) yields 42 without an effect.
;; Returning a print action describes output that occurs during execution.
;;
;; Running:
;;   ./target/debug/cranelisp --run examples/21-hello-io.cl
;;
;;   examples/lib/platforms/ ships a stdio.so symlink to cargo's built
;;   libcranelisp_stdio.so, so on Linux the stdio DLL resolves with no
;;   environment variable. On a host without a matching link, set the
;;   search path instead:
;;     CRANELISP_PLATFORM_PATH=target/debug ./target/debug/cranelisp --run …

;; Platform declaration: load the stdio DLL for print/read-line.
;; This must appear before any platform function imports.
(platform stdio)

;; The built-in functions pure and bind live in `primitives`.
;; Platform functions live in `platform.stdio`.
(import [primitives [pure bind]])
(import [platform.stdio [print]])


;; === Part 1: pure -- lifting values into IO ===

;; primitives/pure is a built-in function that lifts a value into IO.
;; Executing its result yields that value without performing an effect.
;; Type: pure :: (Fn [a] (IO a))
;;
;; The name is conventional for this lift. A function whose result type
;; contains no IO differs from a function returning an IO description.
;; IO has no public constructors, and you cannot pattern-match on it.
;; Use bind to receive an action's result in a continuation returning IO.

(defn check-pure-int []
  ;; (pure 42) creates an (IO Int) value.
  ;; The continuation receives 42 when the runtime executes this action.
  (bind (pure 42) (fn [x] (pure x))))            ;; -> 42

;; pure works with any type -- Bool, String, etc.
(defn check-pure-bool []
  (bind (pure true) (fn [b] (pure (if b 1 0))))) ;; -> 1


;; === Part 2: bind -- chaining IO actions ===

;; bind is the IO sequencing primitive.
;; Type: bind :: (Fn [(IO a) (Fn [a] (IO b))] (IO b))
;;
;; It takes an IO action and a continuation. The continuation
;; receives the inner value of the first action and returns
;; a new IO action. Calling bind only composes them. During execution,
;; the runtime runs the first action, calls the continuation with its
;; result, then runs the action the continuation returns. The result
;; stays in IO: bind cannot turn an (IO a) into a plain a.

(defn check-bind-simple []
  ;; Receive 10, add 5, and lift the result with pure.
  (bind (pure 10) (fn [x] (pure (add-i64 x 5)))))  ;; -> 15

(defn check-bind-chain []
  ;; Chain three steps: start with 1, add 10, then add 100.
  (bind (pure 1)
    (fn [a]
      (bind (pure (add-i64 a 10))
        (fn [b]
          (pure (add-i64 b 100)))))))             ;; -> 111

(defn check-bind-multi-ref []
  ;; The continuation can reference earlier bindings (closures).
  ;; Here we bind three values and combine them all at the end.
  (bind (pure 1)
    (fn [a]
      (bind (pure 2)
        (fn [b]
          (bind (pure 3)
            (fn [c]
              (pure (add-i64 a (add-i64 b c))))))))))  ;; -> 6


;; === Part 3: Conditional IO ===

;; Because IO is a regular type, if-expressions work naturally.
;; Both branches must return the same type -- (IO a) -- so the
;; "do nothing" branch uses pure to lift a default value. Returning a
;; plain integer in that branch would give mismatched branch types.

(defn check-bind-with-if []
  (bind (pure 10)
    (fn [x]
      (if (gt-i64 x 5)
        (pure (add-i64 x 100))                   ;; x > 5: add 100
        (pure x)))))                              ;; -> 110

(defn check-conditional-io []
  ;; Choose between two IO paths based on a condition.
  (bind (pure 7)
    (fn [x]
      (bind (if (gt-i64 x 10)
              (pure (mul-i64 x 2))                ;; big: double
              (pure (add-i64 x 3)))               ;; small: add 3
        (fn [y]
          (pure (add-i64 y 1)))))))               ;; -> 11


;; === Part 4: Building combinators from pure and bind ===
;;
;; The standard library provides combinators like >>, map-io,
;; when-io, etc. Here we build then and map-io from the public functions
;; pure and bind. We compose IO values without inspecting their internals;
;; platform operations supply actions that describe actual effects.

;; then: run two IO actions in sequence, keep the second result.
;; In the standard library this is called `>>`.
(defn then [a b]
  (bind a (fn [_] b)))

(defn check-then []
  ;; (then (pure 999) (pure 42)) discards 999, keeps 42.
  (bind (then (pure 999) (pure 42))
    (fn [x] (pure (add-i64 x 8)))))              ;; -> 50

;; map-io: apply a function whose result contains no IO to the result of an IO action.
;; This avoids writing (bind io (fn [x] (pure (f x)))) everywhere.
(defn map-io [f io-val]
  (bind io-val (fn [x] (pure (f x)))))

(defn square [n] (mul-i64 n n))

(defn check-map-io []
  ;; Squaring the action's result yields 25, then adding 1 yields 26.
  (bind (map-io square (pure 5))
    (fn [x] (pure (add-i64 x 1)))))              ;; -> 26


;; === Part 5: Returning IO from helper functions ===

;; Functions that return IO compose naturally with bind.

(defn add-io [x y]
  (pure (add-i64 x y)))

(defn check-io-helpers []
  (bind (pure 10)
    (fn [a]
      (bind (pure 20)
        (fn [b]
          (add-io a b))))))                       ;; -> 30


;; === Part 6: IO with recursion ===

;; Recursive functions can compose IO actions. The trampoline
;; evaluates bind chains iteratively, so deep chains don't
;; overflow the call stack.

(defn sum-io [n]
  (if (eq-i64 n 0)
    (pure 0)
    (bind (sum-io (sub-i64 n 1))
      (fn [rest] (pure (add-i64 n rest))))))

(defn check-sum-io []
  (sum-io 10))                                   ;; 1+2+...+10 = 55


;; === Part 7: Platform IO -- real side effects ===

;; Now we use the stdio platform to perform actual IO. The `print`
;; function takes a String and returns (IO Int). Calling print performs
;; no output. The runtime writes to stdout when it executes the action.
;;
;; print :: (Fn [String] (IO Int))
;; The return value is 0 (number of bytes is an implementation detail).

(defn check-print-hello []
  ;; The simplest IO program: print a string.
  ;; Side effect: writes "Hello, world!" to stdout.
  (print "Hello, world!"))

(defn check-print-bind []
  ;; Chain two prints with bind. Each print executes in order.
  ;; The continuation receives the result of the previous print
  ;; (always 0) and ignores it with _.
  ;; Side effect: writes "Hello," then "world!" to stdout.
  (bind (print "Hello,")
    (fn [_] (print "world!"))))

(defn check-print-with-result []
  ;; Print a message, then return a computed value.
  ;; bind sequences the effect, then the continuation produces
  ;; a lifted result. Executing the composed action yields 42.
  ;; Side effect: writes "Computing..." to stdout, returns 42.
  (bind (print "Computing...")
    (fn [_] (pure 42))))

(defn greet [name]
  ;; Returning the action from print gives greet an IO result too.
  ;; greet :: (Fn [String] (IO Int))
  ;; IO propagates through the call graph automatically.
  (print name))

(defn check-greet []
  ;; Side effect: writes "Cranelisp" to stdout.
  (greet "Cranelisp"))

(defn check-reuse []
  ;; An IO value describes an effect; it is not the effect itself.
  ;; Calling print and naming its result with let runs nothing. Each time
  ;; the runtime executes the value in the sequence, its effect runs again, so the same value may be used repeatedly.
  ;; Side effect: writes "again" to stdout twice, then returns 7.
  (let [again (print "again")]
    (bind again (fn [_] (bind again (fn [_] (pure 7)))))))


;; --- Expected output ---
;;
;; Parts 1-6 (pure computation, no stdout output):
;;   check-pure-int:       42
;;   check-pure-bool:      1
;;   check-bind-simple:    15
;;   check-bind-chain:     111
;;   check-bind-multi-ref: 6
;;   check-bind-with-if:   110
;;   check-conditional-io: 11
;;   check-then:           50
;;   check-map-io:         26
;;   check-io-helpers:     30
;;   check-sum-io:         55
;;   subtotal:            457
;;
;; Part 7 (platform IO, print returns 0):
;;   check-print-hello:       0
;;   check-print-bind:        0
;;   check-print-with-result: 42
;;   check-greet:             0
;;   check-reuse:             7
;;   subtotal:               49
;;
;; Total: 457 + 49 = 506. The exit code is its low byte: 506 mod 256 = 250.
;;
;; Stdout side effects (in execution order):
;;   Hello, world!
;;   Hello,
;;   world!
;;   Computing...
;;   Cranelisp
;;   again
;;   again

(defn check-introduction []
  (bind (check-pure-int) (fn [r1]
  (bind (check-pure-bool) (fn [r2]
  (bind (check-bind-simple) (fn [r3]
  (bind (check-bind-chain) (fn [r4]
  (bind (check-bind-multi-ref) (fn [r5]
  (bind (check-bind-with-if) (fn [r6]
  (bind (check-conditional-io) (fn [r7]
  (bind (check-then) (fn [r8]
  (bind (check-map-io) (fn [r9]
  (bind (check-io-helpers) (fn [r10]
  (bind (check-sum-io) (fn [r11]
  ;; Part 7: platform IO tests
  (bind (check-print-hello) (fn [r12]
  (bind (check-print-bind) (fn [r13]
  (bind (check-print-with-result) (fn [r14]
  (bind (check-greet) (fn [r15]
  (bind (check-reuse) (fn [r16]
    (pure (add-i64 r1
      (add-i64 r2
        (add-i64 r3
          (add-i64 r4
            (add-i64 r5
              (add-i64 r6
                (add-i64 r7
                  (add-i64 r8
                    (add-i64 r9
                      (add-i64 r10
                        (add-i64 r11
                          (add-i64 r12
                            (add-i64 r13
                              (add-i64 r14
                                (add-i64 r15 r16))))))))))))))))
  )))))))))))))))))))))))))))))))))

;; Recursive application: emit one line per step, then finish.
;; Each recursive call is in the continuation of the preceding print.
(defn print-countdown [n]
  (if (eq-i64 n 0)
    (print "go!")
    (bind (print (int-to-string n))
      (fn [_] (print-countdown (sub-i64 n 1))))))

;; Append 3, 2, 1, go! to the seven stdout lines above.
;; Countdown returns 0, so the sum remains 506 and the exit remains 250.
(defn main []
  (bind (check-introduction)
    (fn [total]
      (bind (print-countdown 3)
        (fn [last] (pure (add-i64 total last)))))))
