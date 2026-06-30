;; serve -- the web connection-lifecycle destructuring wrappers (the cranelisp
;; value SOURCE for the poll leading-pair convention).
;;
;; S96 Chunk B (Wave B4, FIXME 0465). The raw web poll effects take an explicit
;; leading (token, capacity) pair (poll-support.md §3.4/§3.5.2); these friendly
;; verbs destructure the `web/Listener` / `web/Connection` handle ADTs and supply
;; it, keeping the leading-pair plumbing OUT of main.cl (poll-support.md §3.5.3).
;; They place (token, capacity) as the call's leading operands and re-pass the fd
;; as leaf_0; the backend `inject_poll_leading_pair` pass leaves a ResourceSerial
;; leaf's source-supplied pair intact (poll-support.md §3.4.2).
;;
;; This module (not `web`) holds the wrappers because it imports `platform.web`,
;; and the platform load pre-resolves the `web` type-module but NOT `serve` (see
;; web.cl's header for the cycle this avoids). `serve` is loaded AFTER
;; `(platform web)` via main.cl's import.

(import [web [Listener Connection]])
(import [platform.web [bind-listener accept-conn read-conn send-conn]])

;; listen : (Fn [Int Int] (IO Listener)) -- blocking; returns the bound Listener.
(defn listen [port n] (bind-listener port n))

;; accept : (Fn [Listener] (IO Connection)) -- ride the listener fd as the serial
;; admission token (capacity 1); mints a fresh Connection on listener-readable.
(defn accept [listener]
  (match listener
    [(Listener fd pool)
       (accept-conn fd 1 fd)]))

;; read : (Fn [Connection] (IO Request)) -- ride the connection token (capacity 1);
;; the fd is re-passed as leaf_0.
(defn read [conn]
  (match conn
    [(Connection token capacity fd)
       (read-conn token capacity fd)]))

;; send : (Fn [Connection Response] (IO Int)) -- ride the connection token; the fd
;; and the Response are the leaf args.
(defn send [conn resp]
  (match conn
    [(Connection token capacity fd)
       (send-conn token capacity fd resp)]))
