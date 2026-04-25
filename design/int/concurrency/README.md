# Concurrency Diagrams

This directory contains Mermaid diagrams for the **current** and **target**
concurrency architecture, plus focused protocol diagrams for the highest-risk
surfaces.

## Reading order

If you are new to the concurrency design, read these in this order:

1. **`current-state.svg`**
   - High-level picture of the current concurrency architecture.
   - Shows where coordination, worker logic, shared state, and child-crate
     interfaces currently sit.

2. **`target-state.svg`**
   - High-level picture of the intended streamlined target architecture.
   - Shows the desired compartmentalisation: smaller session core, one
     dependency service, one worker subsystem, narrower shared-state ownership.

3. **`concurrency-structure-matrix.svg`**
   - Inventory-style view of the major concurrency structures.
   - For each structure, shows owner, readers/writers, interface shape,
     and current risk level.
   - Best used to decide where design simplification should happen first.

4. **`scheduler-lifecycle.svg`**
   - State-machine view of module lifecycle inside the scheduler.
   - Best for understanding pool transitions and where readiness/publication
     risks attach.

5. **`dependency-protocol-current.svg`**
   - Current dependency publication / registration / wait / resume protocol.
   - Most useful diagram for understanding the current design smell:
     one concurrency protocol implemented across multiple authorities.

6. **`dependency-protocol-target.svg`**
   - Proposed target protocol with a single dependency service.
   - Best used alongside the current version to reason about containment.

7. **`symbol-publication-current.svg`**
   - Current symbol publication and readiness-observation flow.
   - Focuses on the publish-before-read contract between workers,
     symbol tables, typecheck products, and scheduler readiness.

8. **`symbol-publication-target.svg`**
   - Proposed target publication flow with one explicit publication authority.
   - Best used to discuss how to reduce the current publication-risk surface.

## Which diagram answers which question?

### “Where is concurrency architecturally justified?”
Use:
- `current-state.svg`
- `concurrency-structure-matrix.svg`

### “What is the scheduler doing?”
Use:
- `scheduler-lifecycle.svg`

### “Why is dependency handling hard to reason about?”
Use:
- `dependency-protocol-current.svg`
- then compare with `dependency-protocol-target.svg`

### “Why is publish-before-read still risky?”
Use:
- `symbol-publication-current.svg`
- then compare with `symbol-publication-target.svg`

### “What should the target architecture feel like?”
Use:
- `target-state.svg`
- supported by the two `*-target.svg` protocol diagrams

## Design intent of this directory

These diagrams are not intended to replace the prose docs.
They are intended to make three things visible at a glance:

1. **current ownership and coupling**
2. **current protocol complexity**
3. **how the target state reduces concurrency reasoning cost**

The most important use of these diagrams is not just explanation.
It is to help decide whether a concurrency issue should be solved by:
- stronger tests,
- a sharper invariant,
- or a design change that removes or isolates the concurrent surface.

## Source files

Each SVG is generated from the matching `.mmd` file in this directory.
Regenerate with Mermaid CLI, e.g.:

```bash
mmdc -i design/int/concurrency/current-state.mmd -o design/int/concurrency/current-state.svg
```

Or regenerate all diagrams in the directory with a small shell loop.
