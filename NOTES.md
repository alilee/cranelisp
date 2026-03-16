## Issues:
:Int x vs. (:Int x) :(Fn [Int String] String)

## Features:
claude repl
pretty printer
lsp
wasm deployment (repl in browser against wasm platform)
bevy in browser (ecs and w3gpu platform)
web

## Notes:
let’s make a browser-based Rust + Cranelift REPL that:
- Runs in the browser as WebAssembly.
- Accepts a math expression from the user.
- Uses Cranelift to compile it into a new Wasm module in memory.
- Instantiates and runs that Wasm instantly.
- This will be a minimal but working example
