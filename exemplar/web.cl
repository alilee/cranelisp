;; web -- the Request/Response ADTs for the `web` HTTP platform DLL
;; (Sprint 86 Wave E.1, FIXME 0405).
;;
;; Platforms do NOT declare ADTs (platform-interface.md §3a, third
;; convergence). `Request` and `Response` are ordinary `.cl` types; the `web`
;; platform DLL (exemplar/platforms/web/src/lib.rs) only references them by
;; their fully-qualified identities `web/Request` / `web/Response` in the
;; listen/accept/send signatures. The backend generates the schema artifact
;; (web.platform-schema) by walking these deftypes; the host's
;; `/platform-schema web` command regenerates it.
;;
;; This module resolves on the ORDINARY .cl module path (project tree /
;; CRANELISP_LIB), NOT on CRANELISP_PLATFORM_PATH (which locates the dylib).
;;
;; FQ identity: web/Request (single-ctor product, tag 0).
;;   field 0: method : primitives/String  ("GET" | "POST")
;;   field 1: path   : primitives/String  (request path, e.g. "/" or "/solve")
;;   field 2: body   : primitives/String  (raw request body; URL-encoded form
;;                                         data for POST, consumed by
;;                                         form/parse-form-body)
;;
;; FQ identity: web/Response (single-ctor product, tag 0).
;;   field 0: status       : primitives/Int     (HTTP status code, e.g. 200)
;;   field 1: content-type : primitives/String  (e.g. "text/html")
;;   field 2: body         : primitives/String  (response payload)

(deftype Request
  [:primitives/String method :primitives/String path :primitives/String body])

(deftype Response
  [:primitives/Int status :primitives/String content-type :primitives/String body])
