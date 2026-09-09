> [REPL specification index](index.md)

## 12. Demo Trampoline [R4 S23]

The demo player (§10.6) SHOULD support `/quit` within a demo script by restarting the REPL process and continuing with the remaining script lines. This allows demo scripts to demonstrate session restart naturally:

```
; Define something
(defn foo [] 42)
(foo)
; Restart and show it's gone
/quit
; New session starts here
foo
; error: undefined symbol 'foo'
```

When the demo player detects that the REPL process has exited (due to `/quit` or EOF), it SHOULD start a new REPL process and pipe the remaining demo lines into it. The demo ends when the script is exhausted, not when the first REPL exits.
