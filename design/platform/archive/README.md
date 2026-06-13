# design/platform/archive/

Frozen historical platform design docs — superseded by canonical work, kept for context only. Not the target architecture.

| File | Original sprint | What it documented | Why archived |
|---|---|---|---|
| `platform-registry-removal.md` | Sprint 57 (G8) + Sprint 58 addendum | The deletion of `PlatformRegistry` from `int` (`src/platform_registry.rs`) and the cache-restore path that replaced it (DLL re-resolve from persisted `ModuleEntry::PlatformDecl` entries). | Work landed: `PlatformRegistry` is deleted; cache restore is operational. Lessons folded into Decisions 26/27/38, the master `platform.md` §8, and `platform-dlls.md`. Archived per FIXME 0106. |
