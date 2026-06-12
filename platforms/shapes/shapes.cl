;; shapes -- the canonical ADT for the `shapes` platform test-DLL fixture
;; (Sprint 79 Wave 0).
;;
;; Platforms do NOT declare ADTs. `Rectangle` is an ordinary `.cl` type; the
;; `shapes` platform DLL (platforms/shapes/src/lib.rs) only references it by its
;; fully-qualified identity `shapes/Rectangle` in the `area` signature. The
;; backend generates the schema artifact (shapes.platform-schema) by walking
;; this deftype; the host's `/platform-schema shapes` command regenerates it.
;;
;; FQ identity: shapes/Rectangle (single-ctor product, tag 0).
;;   field 0: w : primitives/Int  (offset payload+8)
;;   field 1: h : primitives/Int  (offset payload+16)

(deftype Rectangle [:Int w :Int h])
