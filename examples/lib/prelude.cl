;; examples/lib/prelude.cl — standalone prelude for the examples sequence.
;;
;; This file is NOT the stdlib prelude. It is a minimal, free-standing
;; prelude owned by /examples per root CLAUDE.md §"Stdlib separation":
;; examples MUST NOT depend on stdlib/. This prelude only re-exports the
;; 30 Ring 0/1 primitives that examples use; it does not pull in any
;; traits, macros, or domain modules.
;;
;; Activated by examples/Cranelisp.toml (`lib-dirs = ["./lib"]`) — when
;; `cargo run -- --run examples/FOO.cl` runs, `project_root` is
;; `examples/`, `resolve_prelude` scans the lib dirs, finds this file,
;; and loads it as the implicit prelude.
;;
;; The 30 primitive names mirror the enumeration in
;; design/stdlib/examples-run-path.md §1.3. They coexist with any
;; operator/trait forms an example defines inline (e.g. 15-traits.cl
;; and 19-threading.cl declare their own Num/Eq/Ord traits; they don't
;; rely on this prelude for them).
;;
;; IO examples (21–24) explicitly `(import [primitives [Pure bind]])`
;; and `(import [platform.stdio [...]])`; they do not rely on the
;; prelude for IO names either. Keeping this prelude minimal means the
;; examples themselves demonstrate what's going on — the prelude is a
;; name-surface convenience, not a piece of teaching material.
;;
;; Primitive groups:
;;   Primitive types (so bare `:Int`/`:Float`/`:Bool`/`:String`
;;   annotations resolve without per-file imports — spec 03-types.md
;;   §3.1: bare type refs MUST be re-exported by the prelude or
;;   explicitly imported; FQ `:primitives/Int` is always available):
;;     Int Bool Float String
;;   Int arithmetic + comparison + bool:
;;     add-i64 sub-i64 mul-i64 div-i64
;;     eq-i64 lt-i64 gt-i64 le-i64 ge-i64 not eq-bool
;;   Float arithmetic + comparison:
;;     add-f64 sub-f64 mul-f64 div-f64
;;     eq-f64 lt-f64 gt-f64 le-f64 ge-f64
;;   String:
;;     str-concat str-eq str-len char-at
;;     int-to-string float-to-string bool-to-string
;;   Vec:
;;     vec-len vec-get vec-set vec-push

(export [primitives [Int Bool Float String]])
(export [primitives [add-i64 sub-i64 mul-i64 div-i64
                     eq-i64 lt-i64 gt-i64 le-i64 ge-i64
                     not eq-bool]])
(export [primitives [add-f64 sub-f64 mul-f64 div-f64
                     eq-f64 lt-f64 gt-f64 le-f64 ge-f64]])
(export [primitives [str-concat str-eq str-len char-at
                     int-to-string float-to-string bool-to-string]])
(export [primitives [vec-len vec-get vec-set vec-push]])
