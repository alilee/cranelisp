;; Preamble: import all primitives as bare names.
;;
;; Most tests need bare primitive access (add-i64, str-concat, etc.).
;; This preamble is the standard "I need primitives" setup.

(import [primitives [*]])
