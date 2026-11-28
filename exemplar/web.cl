;; web -- the language-side types of the `web` HTTP platform DLL
;; (exemplar/platforms/web/src/lib.rs), whose effect signatures name them FQ.
;; The DLL's `declare_platform! adts:` arm only validates these names against
;; the generated `web.platform-schema` (`/platform-schema web` regenerates it
;; from these deftypes).
;;
;; This module holds types only and must not import `platform.web`: loading the
;; platform resolves the type modules its signatures reference, this one
;; included, before registering the platform, so that import would be a load
;; cycle. The wrappers live in `serve.cl` (poll-leaf-authoring.md §6).
;;
;; `Connection` is an opaque handle: its `fd` is the accepted socket, from
;; which the platform projects each direction's scheduling token, so no
;; scheduling state rides on the value (poll-leaf-authoring.md §4).
;; `Listener`'s `pool` is the in-flight connection ceiling.

(deftype Listener
  [:primitives/Int fd :primitives/Int pool])

(deftype Connection
  [:primitives/Int fd])

(deftype Request
  [:primitives/String method :primitives/String path :primitives/String body])

(deftype Response
  [:primitives/Int status :primitives/String content-type :primitives/String body])
