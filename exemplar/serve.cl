;; serve -- the web connection-lifecycle convenience wrappers.
;;
;; The wrappers are pass-throughs: the connection handle is opaque (it carries
;; only its `fd`) and the platform projects the token from it
;; (design/platform/poll-leaf-authoring.md §4).
;;
;; This module (not `web`) holds the wrappers because it imports `platform.web`,
;; and the platform load pre-resolves the `web` type-module but NOT `serve` (see
;; web.cl's header and poll-leaf-authoring.md §6 for the load-order rule this
;; avoids).
;; `serve` is loaded AFTER `(platform web)` via main.cl's import.

(import [web [Listener Connection]])
(import [platform.web [bind-listener accept-conn read-conn send-conn]])

;; listen : (Fn [Int Int] (IO Listener)) -- blocking; returns the bound Listener.
(defn listen [port n] (bind-listener port n))

;; accept : (Fn [Listener] (IO Connection)) -- Produce; mints a fresh opaque
;; Connection on listener-readable.
(defn accept [listener] (accept-conn listener))

;; read : (Fn [Connection] (IO Request)) -- Consume; the platform projects the
;; read token from the handle's fd.
(defn read [conn] (read-conn conn))

;; send : (Fn [Connection Response] (IO Int)) -- Consume; the platform projects
;; the write token from the handle's fd.
(defn send [conn resp] (send-conn conn resp))
