;; The inline read/sleep/send handler has a discarded result and a fresh
;; connection token, so it launches independently of the next accept.
(import [prelude []])
(platform web)
(import [primitives [bind sleep str-eq div-i64 int-to-string]])
(import [serve [listen accept]])
(import [platform.web [read-conn send-conn]])
(import [web [Request Response]])

(defn faulty-body [] (int-to-string (div-i64 1 0)))
(defn handle [req]
  (match req
    [(Request method path body)
       (if (str-eq path "/fault")
         (Response 200 "text/html" (faulty-body))
         (Response 200 "text/html" "<html>OK</html>"))]))
(defn slow-ms [req]
  (match req [(Request method path body) (if (str-eq path "/slow") 100 0)]))

(defn serve-loop [listener]
  :(primitives/IO primitives/Int)
  (bind (accept listener)
    (fn [conn]
      (bind
        (bind (read-conn conn)
          (fn [req]
            (bind (sleep (slow-ms req))
              (fn [_] (send-conn conn (handle req))))))
        (fn [_] (serve-loop listener))))))
(defn main [] (bind (listen 8080 64) (fn [listener] (serve-loop listener))))
