;; web -- the connection-handle ADTs for the `web` HTTP platform DLL.
;;
;; S97 ABI v9 (ctx-vtable handle model; design/platform/poll-support.md §3.5,
;; design/arch/effect-concurrency.md §4.1.1). Scheduling state (token/capacity)
;; NEVER rides on a value -- it flows through a trampoline-owned `ctx` vtable the
;; platform's poll-fns call. So `web/Connection` is an OPAQUE handle carrying only
;; the platform's `r` in a GENUINE `fd` field (`r == fd`); the platform reads `fd`
;; back out and PROJECTS the per-direction token from it. No `token`/`capacity`
;; fields (the dead v8 leading-pair shape), no header slot, no descriptor.
;;
;; Platforms still do NOT declare ADTs (platform-interface.md §3a) -- the four
;; `web/*` types are ordinary `.cl` types; the DLL
;; (exemplar/platforms/web/src/lib.rs) references them FQ in the
;; bind-listener/accept-conn/read-conn/send-conn sigs. The backend generates
;; web.platform-schema by walking these deftypes (/platform-schema web).
;;
;; This module is ADTs ONLY -- it carries NO `(import [platform.web ...])` and NO
;; wrappers. WHY: loading the `web` platform DLL pre-resolves the EXTERNAL .cl
;; type-modules its sigs reference (platform-interface.md §7.2 /
;; `src/platform.rs::referenced_sig_modules`) -- i.e. the `web` module -- BEFORE
;; the platform is registered. So if `web` imported `platform.web` it would form a
;; load cycle. The convenience wrappers therefore live in the sibling `serve.cl`
;; module, loaded AFTER `(platform web)` (see serve.cl + main.cl). The general
;; platform-authoring rule is poll-support.md §3.6.3 (model-independent).
;;
;; This module resolves on the ORDINARY .cl module path (project tree /
;; CRANELISP_LIB), NOT on CRANELISP_PLATFORM_PATH (which locates the dylib).
;;
;; FQ identities:
;;   web/Listener   (single-ctor product, tag 0)
;;     fd   : primitives/Int   listener socket fd (accept reads it to poll/accept)
;;     pool : primitives/Int   N, the in-flight-CONNECTION-COUNT ceiling consumed
;;                             by the launch-and-continue fan-out (arch §16).
;;   web/Connection (single-ctor product, tag 0) -- OPAQUE handle (v9)
;;     fd   : primitives/Int   connection socket fd = the platform's `r`; the
;;                             platform reads it back + projects read_tok/write_tok.
;;   web/Request    (single-ctor product, tag 0)  method/path/body : String
;;   web/Response   (single-ctor product, tag 0)  status:Int content-type/body:String

(deftype Listener
  [:primitives/Int fd :primitives/Int pool])

(deftype Connection
  [:primitives/Int fd])

(deftype Request
  [:primitives/String method :primitives/String path :primitives/String body])

(deftype Response
  [:primitives/Int status :primitives/String content-type :primitives/String body])
