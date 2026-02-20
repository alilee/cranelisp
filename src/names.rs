use std::borrow::Borrow;
use std::fmt;
use std::ops::Deref;

use serde::{Deserialize, Serialize};

// ── Name newtypes ─────────────────────────────────────────────────────────

/// Implement common traits for a String newtype wrapper:
/// Deref<Target=str>, Borrow<str>, From<String>, From<&str>,
/// AsRef<str>, PartialEq<str>, PartialEq<&str>.
macro_rules! string_newtype {
    ($name:ident) => {
        impl Deref for $name {
            type Target = str;
            fn deref(&self) -> &str {
                &self.0
            }
        }

        impl Borrow<str> for $name {
            fn borrow(&self) -> &str {
                &self.0
            }
        }

        impl From<String> for $name {
            fn from(s: String) -> Self {
                $name(s)
            }
        }

        impl From<&str> for $name {
            fn from(s: &str) -> Self {
                $name(s.to_string())
            }
        }

        impl AsRef<str> for $name {
            fn as_ref(&self) -> &str {
                &self.0
            }
        }

        impl PartialEq<str> for $name {
            fn eq(&self, other: &str) -> bool {
                self.0 == other
            }
        }

        impl PartialEq<&str> for $name {
            fn eq(&self, other: &&str) -> bool {
                self.0 == *other
            }
        }
    };
}

/// A resolved bare name — the part to the right of `/` in an FQSymbol.
/// Examples: `"print"`, `"add"`, `"None"`.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Symbol(String);
string_newtype!(Symbol);

impl fmt::Display for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

/// Module identity derived from file path relative to project root.
/// Root module has id "", child "util" has id "util", nested "app.handler" etc.
/// Examples: `"platform"`, `"core"`, `"prelude"`, `"core.option"`.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ModuleFullPath(pub String);
string_newtype!(ModuleFullPath);

impl ModuleFullPath {
    pub fn root() -> Self {
        ModuleFullPath(String::new())
    }

    pub fn is_root(&self) -> bool {
        self.0.is_empty()
    }

    /// The short name used for qualified access (e.g. "util" from "app.util").
    /// For root module, returns empty string.
    pub fn short_name(&self) -> &str {
        self.0.rsplit('.').next().unwrap_or(&self.0)
    }
}

impl fmt::Display for ModuleFullPath {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.0.is_empty() {
            write!(f, "<root>")
        } else {
            write!(f, "{}", self.0)
        }
    }
}

/// A trait name, e.g. "Display", "Num".
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct TraitName(String);
string_newtype!(TraitName);

impl fmt::Display for TraitName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

/// A type name, e.g. "Int", "Option", "List".
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct TypeName(String);
string_newtype!(TypeName);

impl fmt::Display for TypeName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

/// A module declaration name from `(mod child)`.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ModuleName(String);
string_newtype!(ModuleName);

impl fmt::Display for ModuleName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

/// A JIT symbol name — the string used to register/look up a function in the JIT symbol table.
/// Examples: `"cranelisp_print"`, `"int-to-string"`, `"cranelisp_op_add"`.
/// Distinct from `Symbol` (user-facing name) to prevent accidental mixing.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct JitSymbol(pub String);
string_newtype!(JitSymbol);

impl fmt::Display for JitSymbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

// ── Fully-qualified symbol ────────────────────────────────────────────────

/// A fully-qualified symbol: a (module, name) pair.
/// Used in `ModuleEntry::Import` and `ModuleEntry::Reexport` to reference
/// a symbol in another module, and returned by `qualified_name()`.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct FQSymbol {
    pub module: ModuleFullPath,
    pub symbol: Symbol,
}

impl FQSymbol {
    pub fn new(module: ModuleFullPath, symbol: Symbol) -> Self {
        FQSymbol { module, symbol }
    }
}

impl fmt::Display for FQSymbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let short = self.module.short_name();
        if short.is_empty() {
            write!(f, "{}", self.symbol)
        } else {
            write!(f, "{}/{}", short, self.symbol)
        }
    }
}

// ── Utility functions ─────────────────────────────────────────────────────

/// Split "Parent.member" → Some(("Parent", "member")).
/// Returns None if no dot present or if either side is empty.
pub fn split_dotted(name: &str) -> Option<(&str, &str)> {
    let dot_pos = name.find('.')?;
    let parent = &name[..dot_pos];
    let member = &name[dot_pos + 1..];
    if parent.is_empty() || member.is_empty() {
        return None;
    }
    Some((parent, member))
}

/// Split "module/local" → Some(("module", "local")).
/// Returns None if no `/` present or if either side is empty.
pub fn split_qualified(name: &str) -> Option<(&str, &str)> {
    let slash_pos = name.find('/')?;
    let module = &name[..slash_pos];
    let local = &name[slash_pos + 1..];
    if module.is_empty() || local.is_empty() {
        return None;
    }
    Some((module, local))
}

/// A parsed name with optional module qualifier.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QualifiedName<'a> {
    pub module: Option<&'a str>,
    pub local: &'a str,
}

/// Parse a name into its module and local parts.
/// "core.option/Option.Some" → { module: Some("core.option"), local: "Option.Some" }
/// "Option.Some" → { module: None, local: "Option.Some" }
/// "foo" → { module: None, local: "foo" }
pub fn parse_name(name: &str) -> QualifiedName<'_> {
    match split_qualified(name) {
        Some((module, local)) => QualifiedName {
            module: Some(module),
            local,
        },
        None => QualifiedName {
            module: None,
            local: name,
        },
    }
}

/// Extract the bare member from a possibly-qualified, possibly-dotted name.
/// "core.option/Option.Some" → "Some" (strip module on `/`, then strip parent on `.`)
/// "Option.Some" → "Some" (existing behavior preserved)
/// "foo" → "foo" (existing behavior preserved)
pub fn resolve_bare_name(name: &str) -> &str {
    // Strip module qualifier first (only if both sides are non-empty)
    let local = match split_qualified(name) {
        Some((_, local)) => local,
        None => name,
    };
    // Then strip type/trait prefix
    match local.rfind('.') {
        Some(pos) => &local[pos + 1..],
        None => local,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // ── split_dotted ───────────────────────────────────────────────────

    #[test]
    fn split_dotted_with_dot() {
        assert_eq!(split_dotted("Option.Some"), Some(("Option", "Some")));
    }

    #[test]
    fn split_dotted_operator() {
        assert_eq!(split_dotted("Num.+"), Some(("Num", "+")));
    }

    #[test]
    fn split_dotted_no_dot() {
        assert_eq!(split_dotted("foo"), None);
    }

    #[test]
    fn split_dotted_empty_parts() {
        assert_eq!(split_dotted(".foo"), None);
        assert_eq!(split_dotted("foo."), None);
    }

    // ── split_qualified ────────────────────────────────────────────────

    #[test]
    fn split_qualified_simple() {
        assert_eq!(
            split_qualified("core.option/Some"),
            Some(("core.option", "Some"))
        );
    }

    #[test]
    fn split_qualified_operator() {
        assert_eq!(split_qualified("core.math/+"), Some(("core.math", "+")));
    }

    #[test]
    fn split_qualified_dotted_local() {
        assert_eq!(
            split_qualified("core.option/Option.Some"),
            Some(("core.option", "Option.Some"))
        );
    }

    #[test]
    fn split_qualified_single_segment_module() {
        assert_eq!(split_qualified("math/add"), Some(("math", "add")));
    }

    #[test]
    fn split_qualified_no_slash() {
        assert_eq!(split_qualified("foo"), None);
    }

    #[test]
    fn split_qualified_empty_module() {
        assert_eq!(split_qualified("/foo"), None);
    }

    #[test]
    fn split_qualified_empty_local() {
        assert_eq!(split_qualified("foo/"), None);
    }

    // ── parse_name ─────────────────────────────────────────────────────

    #[test]
    fn parse_name_bare() {
        assert_eq!(
            parse_name("foo"),
            QualifiedName {
                module: None,
                local: "foo"
            }
        );
    }

    #[test]
    fn parse_name_dotted() {
        assert_eq!(
            parse_name("Option.Some"),
            QualifiedName {
                module: None,
                local: "Option.Some"
            }
        );
    }

    #[test]
    fn parse_name_qualified() {
        assert_eq!(
            parse_name("core.option/Some"),
            QualifiedName {
                module: Some("core.option"),
                local: "Some"
            }
        );
    }

    #[test]
    fn parse_name_qualified_dotted() {
        assert_eq!(
            parse_name("core.option/Option.Some"),
            QualifiedName {
                module: Some("core.option"),
                local: "Option.Some"
            }
        );
    }

    // ── resolve_bare_name ──────────────────────────────────────────────

    #[test]
    fn resolve_bare_name_dotted() {
        assert_eq!(resolve_bare_name("Option.Some"), "Some");
    }

    #[test]
    fn resolve_bare_name_operator() {
        assert_eq!(resolve_bare_name("Num.+"), "+");
    }

    #[test]
    fn resolve_bare_name_plain() {
        assert_eq!(resolve_bare_name("foo"), "foo");
    }

    #[test]
    fn resolve_bare_name_qualified() {
        assert_eq!(resolve_bare_name("core.option/Some"), "Some");
    }

    #[test]
    fn resolve_bare_name_qualified_dotted() {
        assert_eq!(resolve_bare_name("core.option/Option.Some"), "Some");
    }

    #[test]
    fn resolve_bare_name_qualified_operator() {
        assert_eq!(resolve_bare_name("core.math/+"), "+");
    }

    // ── Symbol ────────────────────────────────────────────────────────────

    #[test]
    fn symbol_deref_and_display() {
        let s = Symbol::from("print");
        assert_eq!(&*s, "print");
        assert_eq!(format!("{}", s), "print");
    }

    #[test]
    fn symbol_borrow_str_for_hashmap_lookup() {
        let mut map = std::collections::HashMap::new();
        map.insert(Symbol::from("foo"), 42);
        assert_eq!(map.get("foo"), Some(&42));
    }

    // ── ModuleFullPath ───────────────────────────────────────────────────

    #[test]
    fn module_full_path_deref_and_display() {
        let m = ModuleFullPath::from("prelude");
        assert_eq!(&*m, "prelude");
        assert_eq!(format!("{}", m), "prelude");
    }

    #[test]
    fn module_full_path_borrow_str_for_hashmap_lookup() {
        let mut map = std::collections::HashMap::new();
        map.insert(ModuleFullPath::from("platform"), 42);
        assert_eq!(map.get("platform"), Some(&42));
    }

    #[test]
    fn module_full_path_root() {
        let m = ModuleFullPath::root();
        assert!(m.is_root());
        assert_eq!(format!("{}", m), "<root>");
    }

    #[test]
    fn module_full_path_short_name() {
        assert_eq!(ModuleFullPath::from("prelude").short_name(), "prelude");
        assert_eq!(ModuleFullPath::from("core.option").short_name(), "option");
        assert_eq!(ModuleFullPath::from("app.util.db").short_name(), "db");
    }

    // ── FQSymbol ─────────────────────────────────────────────────────────

    #[test]
    fn fqsymbol_display_with_module() {
        let fq = FQSymbol::new(ModuleFullPath::from("prelude"), Symbol::from("print"));
        assert_eq!(format!("{}", fq), "prelude/print");
    }

    #[test]
    fn fqsymbol_display_nested_module() {
        let fq = FQSymbol::new(ModuleFullPath::from("core.option"), Symbol::from("Some"));
        assert_eq!(format!("{}", fq), "option/Some");
    }

    #[test]
    fn fqsymbol_display_root_module() {
        let fq = FQSymbol::new(ModuleFullPath::root(), Symbol::from("main"));
        assert_eq!(format!("{}", fq), "main");
    }

    #[test]
    fn fqsymbol_equality() {
        let a = FQSymbol::new(ModuleFullPath::from("prelude"), Symbol::from("print"));
        let b = FQSymbol::new(ModuleFullPath::from("prelude"), Symbol::from("print"));
        assert_eq!(a, b);
    }
}
