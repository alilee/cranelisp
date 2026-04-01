// PlatformRegistry: unified registry for platform function pointers and
// scheduling classes (pipeline-v4.md §5.1, Step 8).
//
// Consolidates the scattered `platform_symbols: Vec<(String, *const u8)>` and
// `scheduling_registry: HashMap<Symbol, SchedulingClass>` into a single registry
// keyed by FQSymbol.

use std::collections::HashMap;

use cranelisp_platform::SchedulingClass;
use cranelisp_types::{FQSymbol, JitSymbol, Symbol};

/// A platform function registered from a DLL manifest.
///
/// Stores the JIT-linkable function pointer and the scheduling class
/// for bind-chain independence analysis. Keyed by FQSymbol in the
/// registry (e.g., `platform.stdio/print`).
pub struct PlatformFunction {
    /// JIT symbol name used by `Jit::new_with_symbols` (e.g., "cranelisp_print").
    pub jit_name: JitSymbol,
    /// Function pointer into the loaded DLL.
    pub fn_ptr: *const u8,
    /// Scheduling class from the manifest (Sequential, Commutative, ResourceSerial).
    pub scheduling_class: SchedulingClass,
}

// SAFETY: PlatformFunction contains a raw *const u8 pointing into a loaded DLL.
// The DLL is kept alive for the process lifetime via `loaded_platforms`. The
// pointer is never written through — only passed to JITBuilder::symbol() for
// linking. Send/Sync are needed for the Mutex wrapper on CompilerSession.
unsafe impl Send for PlatformFunction {}
unsafe impl Sync for PlatformFunction {}

/// Registry of all platform functions, keyed by fully qualified symbol.
///
/// Populated during `(platform ...)` form processing. Read-only during
/// codegen and bind-chain analysis. The Mutex wrapper lives on CompilerSession
/// (pipeline-v4.md §5.1), but single-threaded Step 8 accesses it without
/// locking (direct field access before Mutex is added in Step 10).
#[derive(Default)]
pub struct PlatformRegistry {
    entries: HashMap<FQSymbol, PlatformFunction>,
}

impl PlatformRegistry {
    pub fn new() -> Self {
        Self::default()
    }

    /// Register a platform function. Called during platform DLL loading.
    pub fn register(&mut self, fq: FQSymbol, func: PlatformFunction) {
        self.entries.insert(fq, func);
    }

    /// Get the scheduling class for a symbol, for bind-chain analysis.
    ///
    /// Tries bare symbol match across all entries (iterating where
    /// `entry.symbol == symbol`). Platform registries are small
    /// (typically < 20 entries), so linear scan is acceptable.
    pub fn scheduling_class(&self, symbol: &Symbol) -> Option<SchedulingClass> {
        for (fq, func) in &self.entries {
            if fq.symbol == *symbol {
                return Some(func.scheduling_class);
            }
        }
        None
    }

    /// Return JIT symbol pairs for Jit::new_with_symbols().
    ///
    /// Produces `Vec<(&str, *const u8)>` matching the existing codegen API.
    /// This is the primary consumption path during compilation.
    pub fn jit_symbols(&self) -> Vec<(&str, *const u8)> {
        self.entries
            .values()
            .map(|f| (f.jit_name.as_ref(), f.fn_ptr))
            .collect()
    }

    /// Return owned JIT symbol pairs for backward compatibility with
    /// `compile_and_register_defn` which takes `&[(String, *const u8)]`.
    pub fn jit_symbols_owned(&self) -> Vec<(String, *const u8)> {
        self.entries
            .values()
            .map(|f| (f.jit_name.0.clone(), f.fn_ptr))
            .collect()
    }

    /// True if no platform functions are registered.
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }
}

#[cfg(test)]
impl PlatformRegistry {
    /// Create a test registry with synthetic entries.
    pub fn with_test_entries(entries: Vec<(FQSymbol, SchedulingClass)>) -> Self {
        let mut reg = PlatformRegistry::new();
        for (fq, sc) in entries {
            reg.register(
                fq.clone(),
                PlatformFunction {
                    jit_name: JitSymbol::from(format!("test_{}", fq.symbol)),
                    fn_ptr: std::ptr::null(),
                    scheduling_class: sc,
                },
            );
        }
        reg
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use cranelisp_types::ModuleFullPath;

    fn test_fq(module: &str, name: &str) -> FQSymbol {
        FQSymbol {
            module: ModuleFullPath::from(module),
            symbol: Symbol::from(name),
        }
    }

    #[test]
    fn new_registry_is_empty() {
        let reg = PlatformRegistry::new();
        assert!(reg.is_empty());
        assert!(reg.jit_symbols().is_empty());
    }

    #[test]
    fn register_and_lookup() {
        let mut reg = PlatformRegistry::new();
        let fq = test_fq("platform.stdio", "print");
        reg.register(
            fq,
            PlatformFunction {
                jit_name: JitSymbol::from("cranelisp_print"),
                fn_ptr: 0x1000 as *const u8,
                scheduling_class: SchedulingClass::Sequential,
            },
        );
        assert!(!reg.is_empty());
        assert_eq!(
            reg.scheduling_class(&Symbol::from("print")),
            Some(SchedulingClass::Sequential),
        );
        assert_eq!(reg.scheduling_class(&Symbol::from("unknown")), None);
    }

    #[test]
    fn jit_symbols_returns_pairs() {
        let mut reg = PlatformRegistry::new();
        let fq = test_fq("platform.stdio", "print");
        reg.register(
            fq,
            PlatformFunction {
                jit_name: JitSymbol::from("cranelisp_print"),
                fn_ptr: 0x2000 as *const u8,
                scheduling_class: SchedulingClass::Sequential,
            },
        );
        let syms = reg.jit_symbols();
        assert_eq!(syms.len(), 1);
        assert_eq!(syms[0].0, "cranelisp_print");
        assert_eq!(syms[0].1, 0x2000 as *const u8);
    }
}
