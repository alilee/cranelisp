;; 24-io-echo.cl -- Reading input with read-line
;;
;; Example 22 showed print (output). This example introduces read-line
;; (input) and combines both for an echo program.
;;
;;   read-line :: (Fn [] (IO String))
;;
;; read-line returns an IO action that, when forced, reads one line of
;; text. Combined with bind and print, this enables interactive programs.
;;
;; This example uses the test-capture platform, which returns pre-queued
;; strings from read-line instead of reading from the console. With an
;; empty queue, read-line returns "". Swap test-capture for stdio to get
;; real console input.
;;
;; The pattern for read-then-process is:
;;
;;   (bind (read-line) (fn [input]
;;     ... use input ...))
;;
;; Prerequisites:
;;   cargo build -p cranelisp-test-capture
;;   cargo run -- --run examples/24-io-echo.cl

(platform test-capture)
(import [primitives [Pure bind]])
(import [platform.test-capture [print read-line]])


;; === Part 1: Basic read-line ===

;; read-line returns (IO String). We bind it to get the string value.
;; With test-capture and an empty input queue, read-line returns "".

(defn test-read-line-type []
  ;; Verify read-line works by checking we can bind its result.
  ;; Empty input -> str-len "" = 0. Add 1 to prove the bind ran.
  (bind (read-line)
    (fn [input] (Pure (add-i64 (str-len input) 1))))) ;; -> 1


;; === Part 2: Echo -- read then print ===

;; The echo pattern: read a line, then print it back.
;; This chains read-line and print with bind.

(defn echo-once []
  ;; Read a line, print it, return the length of what was read.
  (bind (read-line)
    (fn [input]
      (bind (print input)
        (fn [_] (Pure (add-i64 (str-len input) 1)))))))

(defn test-echo []
  ;; Reads "" (empty queue), prints "", returns 0+1=1.
  (echo-once))                                        ;; -> 1


;; === Part 3: Read and transform ===

;; Read input, transform it with a pure function, then print the result.

(defn echo-with-greeting []
  ;; Prepend "hello, " to the input and print it.
  ;; Return the length of the greeting.
  (bind (read-line)
    (fn [input]
      (let [greeting (str-concat "hello, " input)]
        (bind (print greeting)
          (fn [_] (Pure (str-len greeting))))))))

(defn test-echo-greeting []
  ;; Reads "" -> greeting is "hello, " -> length 7.
  (echo-with-greeting))                               ;; -> 7


;; === Part 4: Multiple reads ===

;; Chain multiple read-line calls. Each bind unwraps one IO String.

(defn read-two-and-combine []
  ;; Read two lines, concatenate them, print the result.
  ;; Return length of combined string + 1.
  (bind (read-line)
    (fn [first]
      (bind (read-line)
        (fn [second]
          (let [combined (str-concat first second)]
            (bind (print combined)
              (fn [_] (Pure (add-i64 (str-len combined) 1))))))))))

(defn test-read-two []
  ;; Both reads return "". Combined is "". Length 0 + 1 = 1.
  (read-two-and-combine))                             ;; -> 1


;; === Part 5: Prompt-read-respond pattern ===

;; A common interactive pattern: print a prompt, read input, respond.

(defn prompt-and-echo []
  ;; Print a prompt, read input, print a welcome message.
  ;; Return the length of the welcome message.
  (bind (print "Enter your name:")
    (fn [_]
      (bind (read-line)
        (fn [name]
          (let [welcome (str-concat "Welcome, " name)]
            (bind (print welcome)
              (fn [_] (Pure (str-len welcome))))))))))

(defn test-prompt []
  ;; Prints "Enter your name:", reads "" (empty queue),
  ;; prints "Welcome, " (9 chars), returns 9.
  (prompt-and-echo))                                  ;; -> 9


;; === Part 6: Conditional on input ===

;; Read input and branch based on its content.

(defn respond-to-input []
  ;; Check if input is empty. Print an appropriate message.
  ;; Return 1 if input was empty, 2 if non-empty.
  (bind (read-line)
    (fn [input]
      (if (eq-i64 (str-len input) 0)
        (bind (print "no input received")
          (fn [_] (Pure 1)))
        (bind (print (str-concat "you said: " input))
          (fn [_] (Pure 2)))))))

(defn test-respond-empty []
  ;; Empty queue -> read-line returns "" -> length 0 -> "no input received"
  (respond-to-input))                                 ;; -> 1


;; --- Expected results ---
;;
;; test-read-line-type:  1
;; test-echo:            1
;; test-echo-greeting:   7
;; test-read-two:        1
;; test-prompt:          9
;; test-respond-empty:   1
;;
;; Total: 1 + 1 + 7 + 1 + 9 + 1 = 20
;;
;; Note: With the test-capture platform and an empty input queue,
;; all read-line calls return "". With the stdio platform, the program
;; would block waiting for console input. To make this example
;; interactive, change (platform test-capture) to (platform stdio)
;; and update the import to [platform.stdio [print read-line]].

(defn main []
  (bind (test-read-line-type) (fn [r1]
  (bind (test-echo) (fn [r2]
  (bind (test-echo-greeting) (fn [r3]
  (bind (test-read-two) (fn [r4]
  (bind (test-prompt) (fn [r5]
  (bind (test-respond-empty) (fn [r6]
    (Pure (add-i64 r1
      (add-i64 r2
        (add-i64 r3
          (add-i64 r4
            (add-i64 r5 r6))))))
  )))))))))))))
