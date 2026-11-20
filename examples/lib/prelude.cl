;; The examples-local prelude re-exports primitive names, without definitions
;; or a stdlib dependency. It loads even for lesson 01, so definitions must
;; live in explicitly imported modules earned by later lessons.
;; See README.md for the earning rule and ../Cranelisp.toml for activation.
;; Primitive types are exported so bare annotations such as :Int resolve.

(export [primitives [Int Bool Float String]])
(export [primitives [add-i64 sub-i64 mul-i64 div-i64
                     eq-i64 lt-i64 gt-i64 le-i64 ge-i64
                     not eq-bool]])
(export [primitives [add-f64 sub-f64 mul-f64 div-f64
                     eq-f64 lt-f64 gt-f64 le-f64 ge-f64]])
(export [primitives [str-concat str-eq str-len char-at
                     int-to-string float-to-string bool-to-string]])
(export [primitives [vec-len vec-get vec-set vec-push]])
;; Pure packages the integer result used by each example's main.
(export [primitives [Pure]])
