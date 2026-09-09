# REPL Experience Specification

Normative specification for the Cranelisp REPL user experience. A conforming REPL MUST satisfy all requirements tagged with the current ring or earlier.

While called repl, the repl experience encompasses the entire user experience from invoking the repl as well as its associated CLI invocation modes, exit codes, batch output format, and cache lifecycle.

## Section map

This index and the linked section files form one normative specification. A
requirement has authority only in its section file; the map below is navigation,
not a second copy of those requirements.

| Section | File |
|---|---|
| 0. CLI Invocation Modes | [00-cli-invocation.md](00-cli-invocation.md) |
| 1. Display Format | [01-display-format.md](01-display-format.md) |
| 2. Prompt | [02-prompt.md](02-prompt.md) |
| 3. Slash Commands | [03-slash-commands.md](03-slash-commands.md) |
| 4. Self-Documentation Contract | [04-self-documentation.md](04-self-documentation.md) |
| 5. Error Presentation | [05-error-presentation.md](05-error-presentation.md) |
| 6. Discoverability | [06-discoverability.md](06-discoverability.md) |
| 7. Performance Targets | [07-performance.md](07-performance.md) |
| 8. Ring 2B Module Demo Scenarios | [08-module-demos.md](08-module-demos.md) |
| 9. Ring Testability Matrix | [09-testability-matrix.md](09-testability-matrix.md) |
| 10. Terminal Styling | [10-terminal-styling.md](10-terminal-styling.md) |
| 11. Ring 3 REPL Requirements | [11-macro-introspection.md](11-macro-introspection.md) |
| 12. Demo Trampoline | [12-demo-trampoline.md](12-demo-trampoline.md) |
| 13. Shell Escape | [13-shell-escape.md](13-shell-escape.md) |
| 14. File Watching | [14-file-watching.md](14-file-watching.md) |
| 15. REPL Session Persistence | [15-session-persistence.md](15-session-persistence.md) |
| 16. Test Discovery and Execution | [16-test-discovery.md](16-test-discovery.md) |
| 17–17.16. Embedded Agent Experience | [17-embedded-agent.md](17-embedded-agent.md) |
| 17.17–17.19. Agent Language Awareness | [17a-agent-language-awareness.md](17a-agent-language-awareness.md) |
| 17.20–17.22. Agent Observability | [17b-agent-observability.md](17b-agent-observability.md) |
| 18. Redefinition Semantics | [18-redefinition.md](18-redefinition.md) |

## Design Principle

> **The REPL reinforces the syntax of the language.** Every output teaches the user how to write Cranelisp.

Output uses the `:Type value` format — the same colon-prefixed type annotation syntax used in the language itself. Names are always fully qualified to teach the module system. Constructors use `Type.Constructor` dot notation (valid input syntax per §1.4.4 of the language spec).
