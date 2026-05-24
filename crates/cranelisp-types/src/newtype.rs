use serde::{Deserialize, Serialize};

/// Generate a string newtype with standard derives and trait impls.
///
/// Derives: Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize
/// Impls: Deref<Target=str>, From<String>, From<&str>, AsRef<str>, Display, Borrow<str>
#[macro_export]
macro_rules! string_newtype {
    ($name:ident) => {
        #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
        pub struct $name(String);

        impl std::ops::Deref for $name {
            type Target = str;
            fn deref(&self) -> &str {
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

        impl std::borrow::Borrow<str> for $name {
            fn borrow(&self) -> &str {
                &self.0
            }
        }

        impl std::fmt::Display for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                f.write_str(&self.0)
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

string_newtype!(Symbol);
string_newtype!(ModuleFullPath);
string_newtype!(TraitName);
string_newtype!(TypeName);
string_newtype!(ModuleName);
string_newtype!(JitSymbol);
string_newtype!(LinkerSymbol);

/// Fully qualified symbol: module path + local name.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct FQSymbol {
    pub module: ModuleFullPath,
    pub symbol: Symbol,
}

impl std::fmt::Display for FQSymbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}/{}", self.module, self.symbol)
    }
}

/// Fully qualified type name: module path + local type name.
///
/// Embeds module context at construction time so downstream consumers
/// (backend match codegen, display, cache) never need reverse lookups.
/// See `design/arch/fqtypename.md` for motivation and migration plan.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct FQTypeName {
    pub module: ModuleFullPath,
    pub name: TypeName,
}

impl FQTypeName {
    pub fn new(module: ModuleFullPath, name: TypeName) -> Self {
        FQTypeName { module, name }
    }
}

impl std::fmt::Display for FQTypeName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}/{}", self.module, self.name)
    }
}

/// Fully qualified trait name: module path + local trait name.
///
/// Eliminates bare `TraitName` collisions in the same way `FQTypeName`
/// eliminates bare `TypeName` collisions. See `design/arch/fqtypename.md`.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct FQTraitName {
    pub module: ModuleFullPath,
    pub name: TraitName,
}

impl FQTraitName {
    pub fn new(module: ModuleFullPath, name: TraitName) -> Self {
        FQTraitName { module, name }
    }
}

impl std::fmt::Display for FQTraitName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}/{}", self.module, self.name)
    }
}

/// Syntactic-stage trait reference — captures **as-written** qualification.
///
/// At the AST stage:
/// - `(impl Display ...)` → `TraitRef { module: None, name: "Display" }`
/// - `(impl fmt/Display ...)` → `TraitRef { module: Some("fmt"), name: "Display" }`
/// - `(impl core.fmt/Display ...)` → `TraitRef { module: Some("core.fmt"), name: "Display" }`
///
/// The `module` field at the syntactic stage may be an import alias OR a full
/// path — whatever the user wrote. Typecheck resolves aliases to the
/// canonical defining-module via the import graph, producing a `FQTraitName`
/// at the resolved-stage boundary per Decision 47.
///
/// `TraitRef` is the **syntactic-stage** counterpart to `FQTraitName` — same
/// structural shape (module + name) but with `Option<ModuleFullPath>` because
/// the syntactic stage captures the user's input directly, including the
/// unqualified case. See `design/arch/facades/types.md` §"Resolved type
/// system" for the producer/consumer split and `spec/02-grammar.md` §2.3.4 /
/// §2.5 + `spec/04-expressions.md` §4.2.2 for the qualified-reference grammar.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct TraitRef {
    pub module: Option<ModuleFullPath>,
    pub name: TraitName,
}

impl TraitRef {
    pub fn new(module: Option<ModuleFullPath>, name: TraitName) -> Self {
        TraitRef { module, name }
    }
}

impl std::fmt::Display for TraitRef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.module {
            None => write!(f, "{}", self.name),
            Some(m) => write!(f, "{}/{}", m, self.name),
        }
    }
}

/// Syntactic-stage type reference — captures **as-written** qualification.
///
/// At the AST stage:
/// - `(Option Int)` → `TypeRef { module: None, name: "Option" }`
/// - `(option/Option Int)` → `TypeRef { module: Some("option"), name: "Option" }`
/// - `(core.option/Option Int)` → `TypeRef { module: Some("core.option"), name: "Option" }`
///
/// Same pattern as `TraitRef`; resolves to `FQTypeName` at typecheck via the
/// import graph per Decision 47. The unqualified case (`module: None`) is the
/// common one; resolution looks the name up against current-scope-plus-imports
/// at the `TypeName → FQTypeName` lift site inside `check_form`.
///
/// `TypeRef` is the **syntactic-stage** counterpart to `FQTypeName` — same
/// structural shape (module + name) but with `Option<ModuleFullPath>` because
/// the syntactic stage captures the user's input directly. See
/// `design/arch/facades/types.md` §"Resolved type system" and `spec/02-grammar.md`
/// §2.3.4 + `spec/04-expressions.md` §4.2.2.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct TypeRef {
    pub module: Option<ModuleFullPath>,
    pub name: TypeName,
}

impl TypeRef {
    pub fn new(module: Option<ModuleFullPath>, name: TypeName) -> Self {
        TypeRef { module, name }
    }
}

impl std::fmt::Display for TypeRef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.module {
            None => write!(f, "{}", self.name),
            Some(m) => write!(f, "{}/{}", m, self.name),
        }
    }
}
