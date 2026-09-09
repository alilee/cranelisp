> [REPL specification index](index.md)

## 9. Ring Testability Matrix

| Requirement | Ring 0 | Ring 1 | Ring 2 | Ring 3 | Ring 4 |
|---|---|---|---|---|---|
| `:Type value` display | Int, Bool, Float, enum ADT | + String, data ADT, Vec, List, closures | + Seq | | + IO |
| Definition display | function type + qualified name | | + constrained, overloaded | + macro | |
| Prompt with timing | yes | | + module name | | |
| `/help` | yes | | | | |
| `/sig`, `/doc`, `/type`, `/info` | yes | | | | |
| `/source`, `/sexp`, `/ast`, `/clif`, `/disasm` | yes | | | | |
| `/list` | Types, Fns | | + Traits, Modules | + Macros | |
| `/time` | yes | | | | |
| `/expand` | | | | yes | |
| `/mod` | | | yes | | |
| Demo trampoline | | | | | yes |
| `/mem` | | yes | | | |
| `/run-tests`, `/run-all-tests` | | | | | yes |
| Shell escape (`/sh`) | | | | | yes |
| File watching | | | | | yes |
| Self-documentation | bare symbol, special forms, operators (qualified) | | + traits, modules | + macros | |
| Error recovery | yes | | | | |
| Startup < 500ms | yes | | | | |
| Eval < 50ms (simple) | yes | | | | |
| Fully-qualified names | all output | | | | |
| `Type.Constructor` notation | yes | | | | |
