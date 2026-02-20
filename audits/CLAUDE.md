# Audits

This directory contains code quality audits of cranelisp modules.

## Running an Audit

To audit a new module, use the following prompt (replacing the module path):

```
Audit the <module> module (`src/<module>/`, or `src/<file>.rs` for single-file modules) for simplicity, maintainability, complexity, duplication, Rust data modeling, and test coverage. Write the audit to `audits/<module>.md`.

Steps:
1. Read all source files in the module to understand structure and responsibilities.
2. Collect file metrics: line counts (`wc -l`), test counts, per-file responsibilities.
3. Identify findings across these categories:
   - **Complexity**: Functions over ~100 lines, deep nesting (3+ indent levels), large match arms
   - **Robustness**: `panic!()`, `.unwrap()`, `.expect()` in non-test code; unreachable fallbacks that mask bugs
   - **Duplication**: Duplications of code and of concepts potentially across modules, repeated patterns that should be extracted
   - **Data modeling**: Stringly-typed patterns, fields that should be grouped, visibility too broad, missing enums
   - **Performance**: Unnecessary clones, linear scans that could be indexed, repeated allocations
   - **Test coverage**: Subsystems with zero unit tests, missing negative tests, duplicated test helpers
4. Rate each finding as High/Medium/Low severity.
5. Include exact file paths and line numbers, code snippets showing the problem, impact description, and a specific recommendation.
6. Write a prioritized improvement plan grouped into phases.
7. Include a verification section with commands to validate changes.
```

## Audit Document Structure

Each audit file follows this structure. See `typechecker.md` for the reference example.

```markdown
# <Module Name> Module Audit

**Module**: `src/<path>/` (<N> files, <N> lines)
**Date**: YYYY-MM-DD
**Scope**: Simplicity, maintainability, complexity, duplication, data modeling, test coverage

## Module Overview
Brief description of what the module does and its role in the pipeline.

### File Metrics
| File | Lines | Responsibility | Tests |
|---|---|---|---|

## Findings

### HIGH-N: <title>
**File**: `<file>:<line_start>-<line_end>`
**Severity**: High (<category>)

Description with code snippets showing the problem.

**Impact**: What goes wrong or what's hard because of this.
**Recommendation**: Specific fix.

### MED-N: <title>
...

### LOW-N: <title>
...

## Prioritized Improvement Plan
### Phase 1: <theme>
### Phase 2: <theme>
...

## Verification
Commands to validate changes after implementation.
```

## Conventions

- **Finding IDs**: Use `HIGH-N`, `MED-N`, `LOW-N` with sequential numbering within each severity level.
- **Severity categories**: Use parenthetical labels — `(maintainability)`, `(complexity)`, `(robustness)`, `(duplication)`, `(data modeling)`, `(performance)`, `(quality assurance)`, `(encapsulation)`, `(code clarity)`, `(consistency)`.
- **Code snippets**: Include abbreviated snippets (elide with `// ...`) showing the structural problem, not full function copies. Always include file path and line numbers.
- **Line references**: Use `file.rs:N` for single lines, `file.rs:N-M` for ranges. Verify line numbers against the actual source before writing.
- **Recommendations**: Be specific and actionable — name the function to extract, the type to change, the field to add. Avoid vague advice like "refactor this."
- **Improvement plan phases**: Group related fixes into themes (e.g., "Panic Removal", "Function Decomposition", "Deduplication", "Data Modeling", "Test Coverage"). Order by priority: safety first, then complexity, then polish.
- **Verification**: Include `just test`, `just check`, and any module-specific validation commands (e.g., grep for remaining panics).

## Completed Audits

| Module | File | Date |
|---|---|---|
| typechecker | `typechecker.md` | 2026-02-13 |
