;; web -- the connection-handle ADTs for the `web` HTTP platform DLL.
;;
;; S96 Chunk B (Wave B4, FIXME 0465 resolution): the v6 single-stream blocking
;; listen/accept/send is replaced by a v8 POLL-shape connection lifecycle
;; (design/platform/poll-support.md §3.5). Platforms still do NOT declare ADTs
;; (platform-interface.md §3a, third convergence) -- the four `web/*` types are
;; ordinary `.cl` types; the DLL (exemplar/platforms/web/src/lib.rs) references
;; them FQ in the bind-listener/accept-conn/read-conn/send-conn sigs. The backend
;; generates web.platform-schema by walking these deftypes (/platform-schema web).
;;
;; This module is ADTs ONLY -- it carries NO `(import [platform.web ...])` and NO
;; wrappers. WHY: loading the `web` platform DLL pre-resolves the EXTERNAL .cl
;; type-modules its sigs reference (platform-interface.md §7.2 /
;; `src/platform.rs::referenced_sig_modules`) -- i.e. the `web` module -- BEFORE
;; the platform is registered. So if `web` imported `platform.web` it would form a
;; load cycle (platform.web load -> resolve web -> web imports platform.web, not
;; yet registered). The destructuring wrappers therefore live in the sibling
;; `serve.cl` module, loaded AFTER `(platform web)` (see serve.cl + main.cl).
;; FIXME 0469 records the §3.5.3 "wrappers in web.cl" depiction as unrealizable.
;;
;; This module resolves on the ORDINARY .cl module path (project tree /
;; CRANELISP_LIB), NOT on CRANELISP_PLATFORM_PATH (which locates the dylib).
;;
;; FQ identities:
;;   web/Listener   (single-ctor product, tag 0)
;;     fd   : primitives/Int   listener socket fd (accept rides it as its serial
;;                             admission token)
;;     pool : primitives/Int   N, the in-flight-CONNECTION-COUNT ceiling consumed
;;                             by the Chunk-B launch-and-continue fan-out (arch §16),
;;                             NOT a per-connection capacity. Inert under the serial loop.
;;   web/Connection (single-ctor product, tag 0)
;;     token    : primitives/Int  per-connection admission token (= fd; fresh per
;;                                accept => distinct connections concurrent, arch §8.2)
;;     capacity : primitives/Int  1 -- serial WITHIN the connection (read->send ordered)
;;     fd       : primitives/Int  connection socket fd (the syscall handle; re-passed leaf_0)
;;   web/Request    (single-ctor product, tag 0)  method/path/body : String
;;   web/Response   (single-ctor product, tag 0)  status:Int content-type/body:String

(deftype Listener
  [:primitives/Int fd :primitives/Int pool])

(deftype Connection
  [:primitives/Int token :primitives/Int capacity :primitives/Int fd])

(deftype Request
  [:primitives/String method :primitives/String path :primitives/String body])

(deftype Response
  [:primitives/Int status :primitives/String content-type :primitives/String body])
