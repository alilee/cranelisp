# user/

User-facing documentation for Cranelisp. Owned by the `/docs` skill.

## Purpose

This directory contains documentation written for Cranelisp users, not implementors:
- Getting-started guide (installation, first program, REPL orientation)
- Language tutorial (progressive introduction to all features)
- Language guide (feature-by-feature reference for practitioners)
- Error message catalog (common errors with explanations and fixes)

## Structure (to be created by /docs)

- `getting-started.md` — Installation, hello world, REPL basics
- `tutorial/` — Progressive introduction; chapters build on each other
- `guide/` — Feature-by-feature reference
- `errors/` — Error message catalog

## Relationship to spec/

The spec (`spec/`) is precise and normative — written for implementors. User documentation is written for programmers using the language: approachable, example-driven, focused on what to do rather than what is formally true.

## For the `/docs` skill

**First session (Phase B)**:
1. Design the tutorial structure: what concepts are introduced in what order?
2. Identify the learning progression: what does a programmer need to know before each concept?
3. Draft the getting-started guide (can write Ring 0 content immediately — it only needs Int, Bool, functions, let, if)
4. Update this CLAUDE.md with the tutorial chapter outline

**Feedback loop**: Report to compiler skills when error messages are confusing, when REPL output is unhelpful, or when a concept has no good introduction path. These are bugs.
