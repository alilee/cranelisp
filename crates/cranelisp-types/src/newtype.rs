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

impl ModuleFullPath {
    /// Derive a dotted module path from a file path relative to a project root.
    ///
    /// `project_root/foo.cl` → `"foo"`
    /// `project_root/core/option.cl` → `"core.option"`
    /// Falls back to file stem if the path is not under project_root.
    pub fn derive_from(path: impl AsRef<std::path::Path>, project_root: impl AsRef<std::path::Path>) -> Self {
        let path = path.as_ref();
        let root = project_root.as_ref();
        if let Ok(rel) = path.strip_prefix(root) {
            let without_ext = rel.with_extension("");
            let dotted = without_ext.components()
                .filter_map(|c| c.as_os_str().to_str())
                .collect::<Vec<_>>()
                .join(".");
            if !dotted.is_empty() {
                return ModuleFullPath(dotted);
            }
        }
        // Fallback: just the file stem.
        let name = path.file_stem()
            .and_then(|s| s.to_str())
            .unwrap_or("user");
        ModuleFullPath(name.to_string())
    }
}

impl From<std::path::PathBuf> for ModuleFullPath {
    fn from(path: std::path::PathBuf) -> Self {
        let name = path.file_stem()
            .and_then(|s| s.to_str())
            .unwrap_or("user");
        ModuleFullPath(name.to_string())
    }
}

impl From<&std::path::Path> for ModuleFullPath {
    fn from(path: &std::path::Path) -> Self {
        let name = path.file_stem()
            .and_then(|s| s.to_str())
            .unwrap_or("user");
        ModuleFullPath(name.to_string())
    }
}
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
