> [REPL specification index](index.md)

## 2. Prompt [Tested]

### 2.1 Primary Prompt [Tested tests/repl_lifecycle::boot_prompt_format_timing_and_module]

The primary prompt MUST display:

```
{compile_ms}+{eval_ms}ms; {module}>
```

Where:
- `compile_ms` — JIT compilation time of the previous expression (integer milliseconds)
- `eval_ms` — evaluation time of the previous expression (integer milliseconds)
- `module` — current module name (default: `user`)

On startup (before any expression), the timing SHOULD be `0+0ms`.


**Ring 0**: timing and prompt display.
**Ring 2**: module name changes when `/mod` switches namespace.

### 2.2 Continuation Prompt [Tested tests/repl_lifecycle::continuation_prompt_for_unclosed_paren]

When multi-line input is in progress (unmatched parentheses or brackets), the continuation prompt MUST be:

```
{spaces}...
```

Where `{spaces}` aligns the `...` with the start of user input on the primary prompt line.

### 2.3 Empty and Comment-Only Input [Tested tests/repl_introspection::empty_input_silent]

Blank lines (empty or whitespace-only) MUST silently re-prompt with no output. The REPL MUST NOT produce an error, evaluation result, or any visible output — it simply presents the next prompt.

Comment-only lines (lines where all non-whitespace content begins with `;`) MUST silently re-prompt with no output. Since `;` is the Cranelisp comment character, a line consisting entirely of comments carries no evaluable content.

This enables:
- Natural use of blank lines and comments as formatting in demo scripts and piped input
- Interactive users pressing Enter on an empty line without seeing an error
- Pasting code blocks that contain comment lines without spurious error output

**Ring 0**: empty and comment-only input handling.
