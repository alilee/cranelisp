;; serve -- the web connection-lifecycle convenience wrappers.
;;
;; S97 ABI v9 (ctx-vtable handle model; design/platform/poll-support.md §3.5.3).
;; Under v9 the wrappers are near-trivial pass-throughs: there is NO leading
;; (token, capacity) pair to thread and NO descriptor to read/write -- the handle
;; is opaque (carries only its `fd`), and the platform poll-fn projects the token
;; from that `fd` and calls `ctx.acquire` itself. So `read`/`send` take the handle
;; directly; `accept` takes the Listener directly.
;;
;; This module (not `web`) holds the wrappers because it imports `platform.web`,
;; and the platform load pre-resolves the `web` type-module but NOT `serve` (see
;; web.cl's header + poll-support.md §3.6.3 for the load-order rule this avoids).
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
