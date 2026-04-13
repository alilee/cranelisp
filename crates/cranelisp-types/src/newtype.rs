use serde::{Deserialize, Serialize};

/// Generate a string newtype with standard derives and trait impls.
///
/// Derives: Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize
/// Impls: Deref<Target=str>, From<String>, From<&str>, AsRef<str>, Display, Borrow<str>
#[macro_export]
macro_rules! string_newtype {
    ($name:ident) => {
        #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
        pub struct $name(pub String);

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
