> [REPL specification index](index.md)

## 8. Ring 2B Module Demo Scenarios [R4 S10]

When the module system is fully wired (Ring 2B), these 7 REPL scenarios validate the module experience. Each scenario has a concrete expected behavior.

**Scenario 1: `/mod math` switches namespace**
```
user> /mod math
math>
```
The prompt changes to reflect the active module. `math` is an existing module, such as
`math.cl` in the project root; `/mod` never creates a module (§3.9). Definitions entered now
belong to `math`. The `/mod` command MUST NOT print a confirmation message — the prompt change is sufficient feedback.

**Scenario 2: `/mod user` switches back**
```
math> /mod user
user>
```
Switching back to `user` restores the default namespace. Previously defined `math` symbols remain accessible via qualified names.

**Scenario 3: `(import [math [foo]])` loads module**
```
user> (import [math [foo]])
```
After defining `foo` in the `math` module (via `/mod math` + `defn`), importing it makes `foo` available as a bare name in `user`.

**Scenario 4: Qualified access `math/foo`**
```
user> math/foo
:(Fn [primitives/Int] primitives/Int) math/foo
```
Without importing, any symbol can be accessed via its qualified path.

**Scenario 5: `/list` shows only definitions**
```
math> /list
Fns:
  foo
```
The `/list` command shows only that module's own definitions — not imports, not special forms. Names are unqualified (they belong to the current module). After switching back to `user` with no definitions:
```
user> /list
(no definitions)
```
`/list` is empty because the user hasn't defined anything yet. Imports and special forms are on `/imports`.

**Scenario 5b: `/imports` shows imports and special forms**
```
user> (import [math [foo]])
user> /imports
Special forms:
  defn deftype fn if let match
Fns:
  foo
```
Special forms always appear in `/imports` (they're available but not user-defined). The imported `foo` appears under Fns. For detail on where imports came from:
```
user> /imports math
From math:
  foo
```
The source module filter groups names by source. Type `foo` for its type signature.

**Scenario 6: `/mod` with no argument returns to the entry module**
```
math> /mod
user>
```
Bare `/mod` with no argument switches back to the entry module (§0.5). The transcript shows a session started without a target, whose entry module is `user`. The current module is always visible in the prompt, so a "show current" command is redundant. `/mod` is the quickest way home.

**Scenario 7: Unknown module gives clear error** [Tested+Neg tests/repl_lifecycle::mod_unknown_module_neg_not_created_and_active_module_unchanged — the error names the module; the prompt, the definition's module and `/exports` show nothing was created, and no file is written]
```
user> /mod nonexistent
Error: Module 'nonexistent' not found.
user>
```
`/mod` never creates a module (§3.9): the error names the missing module, and the prompt stays
on the current module.
