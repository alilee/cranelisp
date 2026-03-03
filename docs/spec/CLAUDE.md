# docs/spec/

Spec files in this directory are the **authoritative record** of what the implemented language does. They document actual behaviour, not aspirational design.

## Conventions

- When adding or changing a feature, update the spec to match the new implementation.
- If the spec and the implementation disagree, the spec is likely stale — investigate and fix whichever is wrong.
- Keywords MUST, MUST NOT, SHOULD, SHOULD NOT, and MAY follow [RFC 2119](https://www.rfc-editor.org/rfc/rfc2119) semantics and describe the current implementation's guarantees.
- Each spec file covers one language feature (e.g. pattern matching, traits, type system).
- Examples in spec files define expected behaviour — they should be testable.
