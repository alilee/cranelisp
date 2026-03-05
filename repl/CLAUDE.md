# repl/

REPL experience specification for Cranelisp. Owned by the `/repl` skill.

## Authority

This directory contains the **normative REPL experience specification** — what a conforming Cranelisp REPL must do from the user's perspective. This is distinct from:

- `spec/` — language spec (owned by `/spec`): defines language semantics, not REPL behavior
- `design/` — implementation design (owned by `/arch` and developer skills): how the REPL is built

The REPL spec defines the **contract between the REPL and the user**: display formats, commands, error presentation, self-documentation, discoverability, and performance. Implementation plans for meeting this contract live in `design/`.

## Files

| File | Contents |
|---|---|
| `CLAUDE.md` | This file — ownership and conventions |
| `spec.md` | Normative REPL experience specification |
| `showcase` | Top-level showcase script — builds binary, plays demos |
| `demos/` | `.demo` scripts, demo player (`demo-player.py`), and `CLAUDE.md` |

## Conventions

- Requirements use RFC 2119 keywords (MUST, SHOULD, MAY)
- Each requirement is testable — it can be verified by an E2E test or REPL session transcript
- Display format examples show exact expected output (whitespace-significant)
- Performance targets are measurable (wall-clock thresholds)
- The spec is ring-aware: requirements are tagged with the ring where they become testable

## For the `/repl` skill

The `/repl` skill owns this directory. When REPL behavior needs to change:
1. Update `repl/spec.md` first (the normative contract)
2. Then update tests and implementation to match

Other skills (especially `/qa`) consume this spec to write REPL experience tests at Layer 4 (E2E).
