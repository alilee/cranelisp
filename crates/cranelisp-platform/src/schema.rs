//! Schema parser + types for the platform-DLL ADT-marshaling surface.
//!
//! A [`Schema`] is the parsed representation of the **compiler-generated
//! schema artifact** a platform DLL embeds via
//! `declare_platform! { schema: include_str!("<name>.platform-schema"), … }`.
//! The artifact is produced by the `/platform-schema <name>` REPL command
//! (backend's `generate_schema`), never hand-authored — it captures the
//! transitive closure of every ADT the platform's function signatures reach,
//! derived from the **resolved module graph** (so the layout it records is the
//! layout the host actually compiles). See
//! `design/arch/platform-interface.md` §5.5 (the field-by-name design,
//! user-ratified 2026-06-07).
//!
//! The parsed schema is consulted at runtime (DLL-side, callback-free) by
//! [`crate::CLAdt`]'s field-access methods to map a field **name** to its byte
//! offset + declared [`FieldType`] (the typed fields drive nested-ADT
//! navigation — `read_field("origin")` learns the field is `geometry/Point`
//! and looks *that* type up in the same map).
//!
//! # Artifact grammar (the generated dialect)
//!
//! The artifact is an S-expression so the generator's emit and this parser
//! agree by construction (`platform-interface.md` §2.2 q-schema-grammar —
//! one dialect, machine-written + machine-read). It mirrors backend's
//! `crates/cranelisp-backend/src/schema.rs` `generate_schema` output:
//!
//! ```text
//! ;; layout-hash: <hex>
//! (schema
//!   (shapes/Rectangle
//!     (Rectangle 0 ((w primitives/Int) (h primitives/Int))))
//!   (geometry/Point
//!     (Point 0 ((x primitives/Int) (y primitives/Int)))))
//! ```
//!
//! - A `;;` line is a comment (the `;; layout-hash:` header is one such — the
//!   hash is exported separately as `__cranelisp_layout_hash_<name>`, so the
//!   parser ignores the comment).
//! - The outer list is `(schema <entry>…)`.
//! - Each `<entry>` is `(<typekey> <ctor>…)` where `<typekey>` is the
//!   structured type-expression key (a bare FQ name `module/Type`, or an
//!   applied form `(module/Type <fieldtype>…)` for a concrete instantiation,
//!   `platform-interface.md` §5.5.3 — never a mangle).
//! - Each `<ctor>` is `(<CtorName> <tag> (<field>…))`; `<field>` is
//!   `(<name> <fieldtype>)`.
//! - `<fieldtype>` ::= `module/Type` (scalar or zero-arg ADT, bare FQ name)
//!   | `(module/Type <fieldtype>…)` (parameterised ADT)
//!   | `(Vec <fieldtype>)`.
//!
//! # Replication, not dependency
//!
//! The parser deliberately does NOT depend on `cranelisp-frontend` (the reader
//! that the *generator* side uses) — making frontend a dep would invert the
//! crate DAG (Principle 3; frontend is upstream of platform). The small S-expr
//! grammar above is replicated here per `platform-interface.md`'s
//! frontend-independence note (§5.5.1). It is intentionally tiny — three token
//! kinds (`(`, `)`, atom) plus `;;` comments.
//!
//! # History
//!
//! Sprint 71 shipped a hand-authored schema *dialect* (`(Type (CLInt w)…)`
//! over `CLInt`/`CLBool`/… field types). That declaration dialect **retired**
//! with the platform-interface rework (FIXME 0286 / `platform-interface.md`
//! §6.6): platforms stop declaring ADTs (their types are ordinary `.cl`
//! modules), and the schema becomes a compiler-generated build artifact. The
//! parser *structure* (two-pass, `ParseLoc` diagnostics, name/field lookups)
//! survives, repointed at the generated artifact grammar.

use std::collections::HashMap;

// ---------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------

/// Source position within a schema artifact — line, column, and raw byte
/// offset for diagnostic display.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ParseLoc {
    pub line: u32,
    pub col: u32,
    pub offset: usize,
}

/// Parsed schema — owned by the DLL via a `LazyLock<Schema>` static
/// (`declare_platform!`'s `schema:` embed arm parses the embedded artifact
/// once), consulted by [`crate::CLAdt`]'s field-access methods to map a field
/// name to its byte offset + declared [`FieldType`].
///
/// Keyed by the **structured type-expression key string** (`shapes/Rectangle`,
/// or `(Option shapes/Rectangle)` for a concrete instantiation) — the same key
/// backend's generator emits (`platform-interface.md` §5.5.3).
#[derive(Debug, Default)]
pub struct Schema {
    types: Vec<TypeShape>,
    by_key: HashMap<String, usize>,
}

/// One schema entry — a type-expression key and its constructor list.
///
/// A product type has one constructor; a sum type lists all of them; an enum's
/// constructors carry empty field lists.
#[derive(Debug, Clone)]
pub struct TypeShape {
    /// The structured type-expression key (`shapes/Rectangle`,
    /// `(Option shapes/Rectangle)`).
    pub key: String,
    pub ctors: Vec<Ctor>,
}

/// A single constructor — its name, heap-node tag (discriminant), and ordered
/// named+typed fields.
#[derive(Debug, Clone)]
pub struct Ctor {
    pub name: String,
    pub tag: u32,
    pub fields: Vec<Field>,
}

/// A single named field, with a resolved (recursive) field type.
#[derive(Debug, Clone)]
pub struct Field {
    pub name: String,
    pub field_type: FieldType,
}

/// Field type — a recursive type-expression (`platform-interface.md` §5.5.2).
///
/// ```text
/// FieldType ::= Scalar(FQTypeName)              ; primitives/Int, primitives/String, …
///             | Adt(FQTypeName, Vec<FieldType>) ; geometry/Point, (Option shapes/Rectangle)
///             | Vec(FieldType)                  ; (Vec primitives/Int)
/// ```
///
/// The recursion lets a field type be a parameterised ADT or a `Vec` of one —
/// the type-expression shapes a `deftype` field can carry. Typed fields are
/// what make nested-ADT navigation work: the field's `FieldType` names the type
/// to look up next in the same schema map.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FieldType {
    /// A scalar leaf — `primitives/Int`, `primitives/Bool`, `primitives/Float`,
    /// `primitives/String`. The layout is the ABI; no schema entry is needed
    /// for the type itself.
    Scalar(String),
    /// A reference to an ADT, possibly with concrete type arguments. The name
    /// + args form the lookup key into the same schema map.
    Adt(String, Vec<FieldType>),
    /// A `Vec` of an element type.
    Vec(Box<FieldType>),
}

impl FieldType {
    /// The four scalar leaf FQ names (their layout is the ABI).
    fn scalar_name(name: &str) -> Option<FieldType> {
        match name {
            "primitives/Int" | "primitives/Bool" | "primitives/Float"
            | "primitives/String" => Some(FieldType::Scalar(name.to_string())),
            _ => None,
        }
    }
}

/// Parse errors for the generated schema artifact. Every variant carries a
/// [`ParseLoc`] for diagnostic display.
///
/// Because the artifact is machine-written, a parse error normally signals a
/// generator/parser grammar drift (a `/dev` bug), not author error — but the
/// diagnostics stay precise to make such drift fast to find.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SchemaParseError {
    UnexpectedEof { expected: &'static str, at: ParseLoc },
    UnexpectedToken { found: String, expected: &'static str, at: ParseLoc },
    UnclosedParen { opened_at: ParseLoc },
    ExtraCloseParen { at: ParseLoc },
    /// The outer list was not `(schema …)`.
    MissingSchemaKeyword { found: String, at: ParseLoc },
    /// A constructor's tag token was not a non-negative integer.
    InvalidTag { found: String, at: ParseLoc },
    /// A field-type token was empty or otherwise unrenderable.
    InvalidFieldType { found: String, at: ParseLoc },
    DuplicateTypeKey { key: String, at: ParseLoc, first_at: ParseLoc },
}

impl std::fmt::Display for SchemaParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnexpectedEof { expected, at } => {
                write!(f, "unexpected EOF (expected {expected}) at line {}, col {}", at.line, at.col)
            }
            Self::UnexpectedToken { found, expected, at } => write!(
                f,
                "unexpected token '{found}' (expected {expected}) at line {}, col {}",
                at.line, at.col
            ),
            Self::UnclosedParen { opened_at } => write!(
                f,
                "unclosed paren opened at line {}, col {}",
                opened_at.line, opened_at.col
            ),
            Self::ExtraCloseParen { at } => {
                write!(f, "extra close-paren at line {}, col {}", at.line, at.col)
            }
            Self::MissingSchemaKeyword { found, at } => write!(
                f,
                "schema artifact must begin '(schema …)', found '{found}' at line {}, col {}",
                at.line, at.col
            ),
            Self::InvalidTag { found, at } => write!(
                f,
                "invalid constructor tag '{found}' (expected a non-negative integer) at line {}, col {}",
                at.line, at.col
            ),
            Self::InvalidFieldType { found, at } => write!(
                f,
                "invalid field type '{found}' at line {}, col {}",
                at.line, at.col
            ),
            Self::DuplicateTypeKey { key, at, first_at } => write!(
                f,
                "duplicate type key '{key}' at line {}, col {} (first declared at line {}, col {})",
                at.line, at.col, first_at.line, first_at.col
            ),
        }
    }
}

impl std::error::Error for SchemaParseError {}

// ---------------------------------------------------------------------
// Schema public API
// ---------------------------------------------------------------------

impl Schema {
    /// Parse a generated schema artifact.
    ///
    /// Empty input (or comments-only — e.g. an artifact carrying only the
    /// `;; layout-hash:` header for a platform that marshals no ADTs) parses to
    /// an empty [`Schema`].
    ///
    /// The grammar is the `(schema (key (Ctor tag (fields)) …) …)` form
    /// emitted by backend's `generate_schema` (module rustdoc). `;;` comment
    /// lines (including the `;; layout-hash:` header) are skipped.
    pub fn parse(src: &str) -> Result<Self, SchemaParseError> {
        let mut parser = Parser::new(src);
        let mut schema = Schema::default();

        parser.skip_ws_and_comments();
        if parser.at_eof() {
            return Ok(schema);
        }

        // Outer list `(schema …)`.
        let outer_open = parser.expect_lparen("'(' starting the schema outer list")?;
        let keyword = parser.parse_atom("the `schema` keyword")?;
        if keyword.text != "schema" {
            return Err(SchemaParseError::MissingSchemaKeyword {
                found: keyword.text,
                at: keyword.at,
            });
        }

        let mut key_locs: HashMap<String, ParseLoc> = HashMap::new();
        loop {
            parser.skip_ws_and_comments();
            match parser.peek() {
                Some(b')') => {
                    parser.bump();
                    break;
                }
                None => return Err(SchemaParseError::UnclosedParen { opened_at: outer_open }),
                _ => {}
            }
            let (shape, at) = parser.parse_type_entry()?;
            if let Some(first_at) = key_locs.get(&shape.key) {
                return Err(SchemaParseError::DuplicateTypeKey {
                    key: shape.key.clone(),
                    at,
                    first_at: *first_at,
                });
            }
            key_locs.insert(shape.key.clone(), at);
            schema.by_key.insert(shape.key.clone(), schema.types.len());
            schema.types.push(shape);
        }

        parser.skip_ws_and_comments();
        if !parser.at_eof() {
            let at = parser.loc();
            return Err(SchemaParseError::UnexpectedToken {
                found: (parser
                    .peek()
                    .expect("byte present — guarded by the !at_eof() check above")
                    as char)
                    .to_string(),
                expected: "end of schema after the outer list",
                at,
            });
        }

        Ok(schema)
    }

    /// Look up a schema entry by its structured type-expression key
    /// (`shapes/Rectangle`, `(Option shapes/Rectangle)`).
    pub fn lookup_type(&self, key: &str) -> Option<&TypeShape> {
        self.by_key.get(key).map(|idx| &self.types[*idx])
    }

    /// Map a (type key, optional ctor name, field name) to the field's byte
    /// offset within the heap payload.
    ///
    /// Layout rule: the u32 tag sits at payload offset 0 (+ 4 bytes pad), so
    /// the *i*-th field lands at offset `8 + i*8`. For a product (single
    /// constructor) `ctor_name` may be `None`; for a sum the caller names the
    /// constructor (e.g. via a dot-qualified `"Some.val"` field name).
    pub fn field_offset(
        &self,
        type_key: &str,
        ctor_name: Option<&str>,
        field_name: &str,
    ) -> Option<usize> {
        let shape = self.lookup_type(type_key)?;
        let ctor = self.select_ctor(shape, ctor_name)?;
        ctor.fields
            .iter()
            .position(|f| f.name == field_name)
            .map(|idx| 8 + idx * 8)
    }

    /// Look up a field's declared [`FieldType`] — drives the type-witness check
    /// and nested-ADT navigation in [`crate::CLAdt`].
    pub fn field_type(
        &self,
        type_key: &str,
        ctor_name: Option<&str>,
        field_name: &str,
    ) -> Option<&FieldType> {
        let shape = self.lookup_type(type_key)?;
        let ctor = self.select_ctor(shape, ctor_name)?;
        ctor.fields.iter().find(|f| f.name == field_name).map(|f| &f.field_type)
    }

    /// Constructor names for a type key (a single self-named ctor for a
    /// product; all variant names for a sum).
    pub fn ctor_names(&self, type_key: &str) -> Option<Vec<&str>> {
        self.lookup_type(type_key)
            .map(|shape| shape.ctors.iter().map(|c| c.name.as_str()).collect())
    }

    /// True if the schema declares no types — a DLL that marshals no ADTs.
    pub fn is_empty(&self) -> bool {
        self.types.is_empty()
    }

    /// Pick the constructor named by `ctor_name`, defaulting to the sole
    /// constructor of a product when `ctor_name` is `None`.
    fn select_ctor<'s>(
        &self,
        shape: &'s TypeShape,
        ctor_name: Option<&str>,
    ) -> Option<&'s Ctor> {
        match ctor_name {
            Some(cn) => shape.ctors.iter().find(|c| c.name == cn),
            None if shape.ctors.len() == 1 => Some(&shape.ctors[0]),
            None => None,
        }
    }
}

// ---------------------------------------------------------------------
// Lexer + parser (private)
// ---------------------------------------------------------------------

/// A parsed atom token with its source position.
struct Atom {
    text: String,
    at: ParseLoc,
}

struct Parser<'a> {
    src: &'a [u8],
    pos: usize,
    line: u32,
    col: u32,
}

impl<'a> Parser<'a> {
    fn new(src: &'a str) -> Self {
        Parser { src: src.as_bytes(), pos: 0, line: 1, col: 1 }
    }

    fn loc(&self) -> ParseLoc {
        ParseLoc { line: self.line, col: self.col, offset: self.pos }
    }

    fn at_eof(&self) -> bool {
        self.pos >= self.src.len()
    }

    fn peek(&self) -> Option<u8> {
        self.src.get(self.pos).copied()
    }

    fn bump(&mut self) -> Option<u8> {
        let b = self.peek()?;
        self.pos += 1;
        if b == b'\n' {
            self.line += 1;
            self.col = 1;
        } else {
            self.col += 1;
        }
        Some(b)
    }

    /// Skip whitespace and `;;`-to-end-of-line comments (the `;; layout-hash:`
    /// header and any other comment lines the generator emits).
    fn skip_ws_and_comments(&mut self) {
        loop {
            match self.peek() {
                Some(b) if b.is_ascii_whitespace() => {
                    self.bump();
                }
                Some(b';') => {
                    // Comment to end of line.
                    while let Some(b) = self.peek() {
                        if b == b'\n' {
                            break;
                        }
                        self.bump();
                    }
                }
                _ => break,
            }
        }
    }

    fn expect_lparen(&mut self, expected: &'static str) -> Result<ParseLoc, SchemaParseError> {
        self.skip_ws_and_comments();
        let at = self.loc();
        match self.peek() {
            Some(b'(') => {
                self.bump();
                Ok(at)
            }
            Some(other) => Err(SchemaParseError::UnexpectedToken {
                found: (other as char).to_string(),
                expected,
                at,
            }),
            None => Err(SchemaParseError::UnexpectedEof { expected, at }),
        }
    }

    /// True if `b` ends an atom (whitespace, paren, comment-start, or EOF).
    fn is_atom_terminator(b: u8) -> bool {
        b.is_ascii_whitespace() || b == b'(' || b == b')' || b == b';'
    }

    /// Parse a bare atom (no parens). Errors on EOF or an immediate `(`/`)`.
    fn parse_atom(&mut self, expected: &'static str) -> Result<Atom, SchemaParseError> {
        self.skip_ws_and_comments();
        let at = self.loc();
        match self.peek() {
            None => return Err(SchemaParseError::UnexpectedEof { expected, at }),
            Some(b'(') | Some(b')') => {
                return Err(SchemaParseError::UnexpectedToken {
                    found: (self
                        .peek()
                        .expect("byte present — matched Some(b'(')|Some(b')') above")
                        as char)
                        .to_string(),
                    expected,
                    at,
                });
            }
            _ => {}
        }
        let start = self.pos;
        while let Some(b) = self.peek() {
            if Self::is_atom_terminator(b) {
                break;
            }
            self.bump();
        }
        // SAFETY: the artifact is UTF-8 (parsed from a Rust &str) and atoms
        // never split a code point — atom terminators are all ASCII.
        let text = std::str::from_utf8(&self.src[start..self.pos])
            .unwrap_or_default()
            .to_string();
        Ok(Atom { text, at })
    }

    /// Parse one `(typekey ctor…)` entry. The cursor is at the opening `(`.
    fn parse_type_entry(&mut self) -> Result<(TypeShape, ParseLoc), SchemaParseError> {
        let open = self.expect_lparen("'(' starting a type entry")?;
        let key = self.parse_type_key()?;

        let mut ctors = Vec::new();
        loop {
            self.skip_ws_and_comments();
            match self.peek() {
                Some(b')') => {
                    self.bump();
                    break;
                }
                None => return Err(SchemaParseError::UnclosedParen { opened_at: open }),
                _ => {}
            }
            ctors.push(self.parse_ctor()?);
        }
        Ok((TypeShape { key, ctors }, open))
    }

    /// Parse a type-expression **key** — a bare FQ name or an applied
    /// `(module/Type fieldtype…)` form — and render it back to canonical text
    /// (the same text backend's generator emits, so the keys match by
    /// construction).
    fn parse_type_key(&mut self) -> Result<String, SchemaParseError> {
        self.skip_ws_and_comments();
        match self.peek() {
            Some(b'(') => {
                // Applied form — parse as a FieldType and render it.
                let ft = self.parse_field_type()?;
                Ok(render_field_type(&ft))
            }
            _ => {
                let atom = self.parse_atom("a type-expression key")?;
                Ok(atom.text)
            }
        }
    }

    /// Parse one `(CtorName tag (field…))` constructor. Cursor at the `(`.
    fn parse_ctor(&mut self) -> Result<Ctor, SchemaParseError> {
        let open = self.expect_lparen("'(' starting a constructor")?;
        let name = self.parse_atom("a constructor name")?;
        let tag_atom = self.parse_atom("a constructor tag")?;
        let tag: u32 = tag_atom.text.parse().map_err(|_| SchemaParseError::InvalidTag {
            found: tag_atom.text.clone(),
            at: tag_atom.at,
        })?;

        // Field list `(field…)`.
        let fields_open = self.expect_lparen("'(' starting the field list")?;
        let mut fields = Vec::new();
        loop {
            self.skip_ws_and_comments();
            match self.peek() {
                Some(b')') => {
                    self.bump();
                    break;
                }
                None => return Err(SchemaParseError::UnclosedParen { opened_at: fields_open }),
                _ => {}
            }
            fields.push(self.parse_field()?);
        }

        // Close the constructor list.
        self.skip_ws_and_comments();
        match self.peek() {
            Some(b')') => {
                self.bump();
            }
            None => return Err(SchemaParseError::UnclosedParen { opened_at: open }),
            Some(other) => {
                let at = self.loc();
                return Err(SchemaParseError::UnexpectedToken {
                    found: (other as char).to_string(),
                    expected: "')' closing the constructor",
                    at,
                });
            }
        }

        Ok(Ctor { name: name.text, tag, fields })
    }

    /// Parse one `(name fieldtype)` field pair. Cursor at the `(`.
    fn parse_field(&mut self) -> Result<Field, SchemaParseError> {
        let open = self.expect_lparen("'(' starting a field")?;
        let name = self.parse_atom("a field name")?;
        let field_type = self.parse_field_type()?;
        self.skip_ws_and_comments();
        match self.peek() {
            Some(b')') => {
                self.bump();
            }
            None => return Err(SchemaParseError::UnclosedParen { opened_at: open }),
            Some(other) => {
                let at = self.loc();
                return Err(SchemaParseError::UnexpectedToken {
                    found: (other as char).to_string(),
                    expected: "')' closing the field",
                    at,
                });
            }
        }
        Ok(Field { name: name.text, field_type })
    }

    /// Parse a [`FieldType`]: a bare FQ name (scalar or zero-arg ADT) or an
    /// applied `(module/Type ft…)` / `(Vec ft)` form.
    fn parse_field_type(&mut self) -> Result<FieldType, SchemaParseError> {
        self.skip_ws_and_comments();
        match self.peek() {
            Some(b'(') => {
                let open = self.expect_lparen("'(' starting a field type")?;
                let head = self.parse_atom("a type name in an applied field type")?;
                let mut args = Vec::new();
                loop {
                    self.skip_ws_and_comments();
                    match self.peek() {
                        Some(b')') => {
                            self.bump();
                            break;
                        }
                        None => {
                            return Err(SchemaParseError::UnclosedParen { opened_at: open });
                        }
                        _ => {}
                    }
                    args.push(self.parse_field_type()?);
                }
                if head.text == "Vec" {
                    let elem = args.into_iter().next().ok_or(SchemaParseError::InvalidFieldType {
                        found: "(Vec)".to_string(),
                        at: open,
                    })?;
                    Ok(FieldType::Vec(Box::new(elem)))
                } else {
                    Ok(FieldType::Adt(head.text, args))
                }
            }
            _ => {
                let atom = self.parse_atom("a field type")?;
                if atom.text.is_empty() {
                    return Err(SchemaParseError::InvalidFieldType {
                        found: atom.text,
                        at: atom.at,
                    });
                }
                Ok(FieldType::scalar_name(&atom.text)
                    .unwrap_or_else(|| FieldType::Adt(atom.text, Vec::new())))
            }
        }
    }
}

/// Render a [`FieldType`] back to its canonical artifact text — used to
/// re-render an applied type-expression *key* so it matches the generator's
/// emitted key string by construction.
fn render_field_type(ft: &FieldType) -> String {
    match ft {
        FieldType::Scalar(name) => name.clone(),
        FieldType::Adt(name, args) if args.is_empty() => name.clone(),
        FieldType::Adt(name, args) => {
            let arg_strs: Vec<String> = args.iter().map(render_field_type).collect();
            format!("({name} {})", arg_strs.join(" "))
        }
        FieldType::Vec(elem) => format!("(Vec {})", render_field_type(elem)),
    }
}

// ---------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------

#[cfg(test)]
mod tests;
