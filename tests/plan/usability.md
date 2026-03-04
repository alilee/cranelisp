# Usability Register

Structured destination for findings from user-proxy skills. When `/stdlib`, `/examples`, `/docs`, `/port`, `/repl`, or `/platform` encounter corner cases, unhelpful errors, inference friction, missing APIs, or ergonomic issues, they file findings here rather than routing ad-hoc to individual compiler skills. `/qa` triages findings and routes them to the responsible skill.

**Blocking findings are part of the ring gate** -- a ring cannot advance if any blocking usability finding remains unresolved.

---

## Filing Process

1. **User-proxy skill encounters friction** while exercising the language from their perspective (library author, learner, documentation writer, application developer, interactive user, extension author).
2. **Skill files a finding** in the appropriate ring section below, using the template.
3. **`/qa` triages** the finding: assigns severity, identifies the responsible compiler skill, and adds it to the ring gate checklist.
4. **Responsible skill addresses** the finding (fix, workaround, or reasoned deferral).
5. **`/qa` verifies** the resolution and marks the finding as resolved, recording the ring and commit.

---

## Filing Template

Each finding includes:

| Field | Description |
|---|---|
| **ID** | `U{ring}.{seq}` -- e.g. `U0.1`, `U2.3` |
| **Source skill** | Which user-proxy skill encountered it (`/stdlib`, `/examples`, `/docs`, `/port`, `/repl`, `/platform`) |
| **Category** | One of: `error quality`, `inference friction`, `missing API`, `performance`, `ergonomics`, `discoverability`, `other` |
| **Severity** | `blocking` (must fix before ring advance), `important` (should fix), `deferred` (nice to have) |
| **Description** | What happened, what was expected, what would be better |
| **Responsible skill** | Which compiler skill should address it (if known) |
| **Status** | `open`, `in-progress`, `resolved`, `wont-fix` |
| **Resolution** | How it was resolved, with ring and commit reference |

### Who Contributes

| Skill | Perspective | Typical Findings |
|---|---|---|
| `/stdlib` | Library author | Missing primitives, awkward trait APIs, naming surprises |
| `/examples` | Learner | Confusing errors, non-obvious syntax, missing affordances |
| `/docs` | New user advocate | Learning curve gaps, terminology inconsistencies |
| `/port` | Application developer | Scale issues, module friction, stdlib gaps, IO model limits |
| `/repl` | Interactive user | Discoverability gaps, feedback quality, latency |
| `/platform` | Extension author | C-ABI awkwardness, marshalling pain, IO model leaks |

### What Gets Registered

- Corner cases where language behavior is surprising or unintuitive
- Unhelpful or misleading error messages
- Type inference that requires too many annotations
- Missing stdlib functions that real code needs
- Macro system limitations encountered in practice
- REPL experience gaps (discoverability, feedback, performance)
- Module system friction (import patterns, visibility surprises)
- Performance problems at realistic scale
- Platform/FFI ergonomic issues

---

## Ring 0: Core

*No findings yet.*

---

## Ring 1: Heap

*No findings yet.*

---

## Ring 2: Abstraction

*No findings yet.*

---

## Ring 3: Meta

*No findings yet.*

---

## Ring 4: Effects

*No findings yet.*
