;; web_poll fixture -- a MINIMAL free-standing poll-shape web server for the §3A
;; single-serial-roundtrip e2e (tests/exemplar_web_poll.rs).
;;
;; S96 Chunk B (Wave B4, FIXME 0465). Exercises the v8 poll-shape web platform
;; (bind-listener blocking + accept-conn/read-conn/send-conn poll leaves) under
;; the SERIAL serve loop -- the Chunk-A baseline (the fan-out is Chunk B). Unlike
;; the Sudoku exemplar, this fixture is FREE-STANDING (zero stdlib dependency, no
;; prelude / trait operators): the router ignores the request and returns a fixed
;; response, so the test asserts purely that the poll accept->read->send arc
;; serves one roundtrip. The port is parametrized (the test rewrites the
;; `(defn port [] ...)` line) so it never collides with exemplar_web.rs's 8080
;; in shared lanes (Gap G4).

(platform web)

;; Friendly serve verbs (serve.cl destructures the handles + supplies the poll
;; leading pair) + the Request/Response ADTs (web.cl). bind/Pure from primitives.
(import [serve [listen accept read send]])
(import [web [Request Response]])
(import [primitives [bind Pure]])

;; The pure router -- fixed response (no routing, so no `=`/stdlib needed). The
;; body is the marker the e2e asserts.
(defn handle [req]
  (Response 200 "text/plain" "hello-from-poll-web"))

;; handle-conn : (Fn [Connection] (IO Int)) -- one connection: read -> handle -> send.
(defn handle-conn [conn]
  (bind (read conn)
    (fn [req]
      (send conn (handle req)))))

;; SERIAL accept -> handle-conn -> recur; TCO'd (fan-out-ready, but serial here).
(defn serve-loop [listener]
  :(primitives/IO primitives/Int)
  (bind (accept listener)
    (fn [conn]
      (bind (handle-conn conn)
        (fn [_] (serve-loop listener))))))

;; Parametrized port -- the test rewrites this line to a probed free port.
(defn port [] 18080)
(defn pool-size [] 8)

(defn main []
  (bind (listen (port) (pool-size))
    (fn [listener] (serve-loop listener))))
