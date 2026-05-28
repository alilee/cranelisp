//! Schema parser + types for the platform-DLL ADT-marshaling surface.
//!
//! A `Schema` is a parsed representation of the cranelisp-S-expression
//! schema literal embedded in `declare_platform! { schema: "...", ... }`.
//! It is consulted at runtime (DLL-side, callback-free) by `CLAdt<T>`'s
//! field-access methods to compute byte offsets and validate field types.
//!
//! See `design/platform/sprint71-redesign.md` §1–§2 for the BNF, lexical
//! conventions, error grammar, and parser strategy. The reserved CL
//! wrapper set is `{CLInt, CLBool, CLFloat, CLString}` this sprint;
//! `CLIO` is reserved-but-not-parseable (rejected at parse time as a
//! reserved-for-future field type).
//!
//! The parser does NOT depend on `cranelisp-frontend` — keeping the DAG
//! clean per Principle 3 (frontend is upstream of platform; making it a
//! dep would invert the DAG).

use std::collections::HashMap;

// ---------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------

/// Source position within a schema literal — line, column, and raw byte
/// offset for diagnostic display.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ParseLoc {
    pub line: u32,
    pub col: u32,
    pub offset: usize,
}

impl ParseLoc {
    fn start() -> Self {
        ParseLoc { line: 1, col: 1, offset: 0 }
    }
}

/// Parsed schema — owned by the DLL via a `LazyLock<Schema>` static,
/// consulted by `CLAdt<T>::read_field` to compute byte offsets.
///
/// `Schema::parse` is fallible per the cranelisp-S-expr grammar in
/// `design/platform/sprint71-redesign.md` §1.1.
#[derive(Debug)]
pub struct Schema {
    types: Vec<TypeShape>,
    by_name: HashMap<String, usize>,
}

/// A single declared type — product (one variant) or sum (multiple variants).
#[derive(Debug, Clone)]
pub struct TypeShape {
    pub name: String,
    pub variants: Vec<Variant>,
}

/// A single variant — anonymous for products (one variant named after the
/// type itself), named for sums.
#[derive(Debug, Clone)]
pub struct Variant {
    pub name: String,
    pub fields: Vec<Field>,
}

/// A single named field, with a resolved field type.
#[derive(Debug, Clone)]
pub struct Field {
    pub name: String,
    pub field_type: FieldType,
}

/// Field type — one of the four reserved CL wrappers or a reference to
/// another declared ADT in the same schema.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FieldType {
    CLInt,
    CLBool,
    CLFloat,
    CLString,
    /// Reference to a type-name declared elsewhere in the same schema.
    Adt(String),
}

/// Parse errors per `design/platform/sprint71-redesign.md` §1.7. Every
/// variant carries a `ParseLoc` for diagnostic display.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SchemaParseError {
    UnexpectedEof { expected: &'static str, at: ParseLoc },
    UnexpectedToken { found: String, expected: &'static str, at: ParseLoc },
    UnclosedParen { opened_at: ParseLoc },
    ExtraCloseParen { at: ParseLoc },
    InvalidIdentifier { found: String, at: ParseLoc, reason: &'static str },
    /// User attempted to redefine a reserved CL wrapper name (e.g. `CLInt`)
    /// as a user-declared ADT type.
    ReservedTypeName { name: String, at: ParseLoc },
    /// `CLIO` named as a field type — reserved for future use; not
    /// permitted as a schema field this sprint.
    ReservedFieldTypeNotYetSupported { name: &'static str, at: ParseLoc },
    DuplicateTypeName { name: String, at: ParseLoc, first_at: ParseLoc },
    /// Field-type identifier neither names a CL wrapper nor a declared type.
    UnknownFieldType { name: String, at: ParseLoc },
    /// `()` appeared where a variant clause was expected.
    EmptyVariantClause { at: ParseLoc },
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
            Self::InvalidIdentifier { found, at, reason } => write!(
                f,
                "invalid identifier '{found}' at line {}, col {} ({reason})",
                at.line, at.col
            ),
            Self::ReservedTypeName { name, at } => write!(
                f,
                "reserved type name '{name}' cannot be redefined at line {}, col {} \
                 (reserved CL wrappers: CLInt, CLBool, CLFloat, CLString, CLIO)",
                at.line, at.col
            ),
            Self::ReservedFieldTypeNotYetSupported { name, at } => write!(
                f,
                "field type '{name}' is reserved for future use and not yet \
                 supported as a schema field at line {}, col {}",
                at.line, at.col
            ),
            Self::DuplicateTypeName { name, at, first_at } => write!(
                f,
                "duplicate type name '{name}' at line {}, col {} (first declared at line {}, col {})",
                at.line, at.col, first_at.line, first_at.col
            ),
            Self::UnknownFieldType { name, at } => write!(
                f,
                "unknown field type '{name}' at line {}, col {} (not a CL wrapper or declared ADT)",
                at.line, at.col
            ),
            Self::EmptyVariantClause { at } => {
                write!(f, "empty variant clause '()' at line {}, col {}", at.line, at.col)
            }
        }
    }
}

impl std::error::Error for SchemaParseError {}

// ---------------------------------------------------------------------
// Schema public API
// ---------------------------------------------------------------------

impl Schema {
    /// Parse a schema literal per `design/platform/sprint71-redesign.md` §1.
    /// Empty input parses to an empty `Schema` (a DLL that declares no
    /// ADT-marshaling functions has nothing to declare).
    ///
    /// The schema is wrapped in one outer `(...)` list containing zero or
    /// more `(TypeName ...)` declarations — no leading `schema` keyword
    /// per §1.6.
    pub fn parse(src: &str) -> Result<Self, SchemaParseError> {
        let mut parser = Parser::new(src);
        let mut schema = Schema { types: Vec::new(), by_name: HashMap::new() };
        let mut decl_locs: HashMap<String, ParseLoc> = HashMap::new();

        parser.skip_ws_and_comments();

        // Empty input (or comments-only) → empty schema.
        if parser.at_eof() {
            return Ok(schema);
        }

        // Outer list `(...)` wraps the type-decl sequence.
        let outer_open = parser.expect_lparen("'(' starting the schema's outer list")?;

        // Pass 1: read all top-level type-decls; capture field-type names
        // as raw strings to be resolved in pass 2.
        loop {
            parser.skip_ws_and_comments();
            if let Some(b')') = parser.peek() {
                parser.bump();
                break;
            }
            if parser.at_eof() {
                return Err(SchemaParseError::UnclosedParen { opened_at: outer_open });
            }
            let (shape, loc) = parser.parse_type_decl(&decl_locs)?;
            if let Some(first_at) = decl_locs.get(&shape.name) {
                return Err(SchemaParseError::DuplicateTypeName {
                    name: shape.name.clone(),
                    at: loc,
                    first_at: *first_at,
                });
            }
            decl_locs.insert(shape.name.clone(), loc);
            schema.by_name.insert(shape.name.clone(), schema.types.len());
            schema.types.push(shape);
        }

        // Reject trailing garbage after the outer list.
        parser.skip_ws_and_comments();
        if !parser.at_eof() {
            let at = parser.loc();
            return Err(SchemaParseError::UnexpectedToken {
                found: (parser.peek().unwrap() as char).to_string(),
                expected: "end of schema after outer list",
                at,
            });
        }

        // Pass 2: resolve field-type strings against (reserved CL wrappers)
        // ∪ (declared type names). Self- and forward-references resolve here.
        let known: Vec<String> = schema.types.iter().map(|t| t.name.clone()).collect();
        for shape in &mut schema.types {
            for variant in &mut shape.variants {
                for field in &mut variant.fields {
                    if let FieldType::Adt(name) = &field.field_type {
                        if !known.iter().any(|n| n == name) {
                            // Unresolved: not a CL wrapper (those resolved
                            // in pass 1) and not declared in the schema.
                            // We don't have the original ParseLoc by this
                            // point — emit synthetic and rely on the name
                            // for diagnostics. The pass-1 parser will have
                            // caught most lexical errors before reaching here.
                            return Err(SchemaParseError::UnknownFieldType {
                                name: name.clone(),
                                at: ParseLoc::start(),
                            });
                        }
                    }
                }
            }
        }

        Ok(schema)
    }

    /// Look up a type by name.
    pub fn lookup_type(&self, name: &str) -> Option<&TypeShape> {
        self.by_name.get(name).map(|idx| &self.types[*idx])
    }

    /// Look up a field on a product type. For sum types, use
    /// `lookup_variant_field_offset` with the variant name.
    ///
    /// Returns the byte offset of the field within the heap payload
    /// (per the documented layout rule — tag at offset 0, fields at
    /// 8-byte slots starting at offset 8). Returns `None` if the
    /// type/field is not declared.
    ///
    /// Per design §4.4, this method accepts dot-qualified names for
    /// product types as a uniform syntactic convenience
    /// (`"Rectangle.w"` works alongside `"w"`).
    pub fn lookup_field_offset(&self, type_name: &str, field_name: &str) -> Option<usize> {
        let shape = self.lookup_type(type_name)?;
        if shape.variants.len() != 1 {
            // Sum types: caller must use lookup_variant_field_offset with
            // dot-qualified name.
            return None;
        }
        let variant = &shape.variants[0];
        // Strip the optional product-name qualifier (`Rectangle.w` → `w`).
        let canonical = field_name
            .strip_prefix(&format!("{}.", shape.name))
            .unwrap_or(field_name);
        for (idx, field) in variant.fields.iter().enumerate() {
            if field.name == canonical {
                // Tag at offset 0 (4 bytes) + 4 bytes pad → fields at
                // 8-byte slots starting at offset 8.
                return Some(8 + idx * 8);
            }
        }
        None
    }

    /// Look up a field on a specific variant of a sum type. Returns the
    /// byte offset within the heap payload (tag at offset 0, fields at
    /// 8-byte slots starting at offset 8).
    pub fn lookup_variant_field_offset(
        &self,
        type_name: &str,
        variant_name: &str,
        field_name: &str,
    ) -> Option<usize> {
        let shape = self.lookup_type(type_name)?;
        let variant = shape.variants.iter().find(|v| v.name == variant_name)?;
        for (idx, field) in variant.fields.iter().enumerate() {
            if field.name == field_name {
                return Some(8 + idx * 8);
            }
        }
        None
    }

    /// Look up a field's declared type — used by `read_field`/`own_field`
    /// to verify the user's witness `F` against the schema.
    pub fn lookup_field_type(
        &self,
        type_name: &str,
        variant_name: Option<&str>,
        field_name: &str,
    ) -> Option<&FieldType> {
        let shape = self.lookup_type(type_name)?;
        let variant = if let Some(vn) = variant_name {
            shape.variants.iter().find(|v| v.name == vn)?
        } else if shape.variants.len() == 1 {
            &shape.variants[0]
        } else {
            return None;
        };
        variant.fields.iter().find(|f| f.name == field_name).map(|f| &f.field_type)
    }

    /// Variant names for a sum type (or `[type_name]` for a product).
    pub fn variant_names(&self, type_name: &str) -> Option<Vec<&str>> {
        self.lookup_type(type_name)
            .map(|shape| shape.variants.iter().map(|v| v.name.as_str()).collect())
    }

    /// True if the schema declares no types — useful for DLLs that don't
    /// use ADT marshaling.
    pub fn is_empty(&self) -> bool {
        self.types.is_empty()
    }
}

// ---------------------------------------------------------------------
// Lexer + parser (private)
// ---------------------------------------------------------------------

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
        if self.at_eof() { None } else { Some(self.src[self.pos]) }
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

    fn skip_ws_and_comments(&mut self) {
        loop {
            match self.peek() {
                Some(b' ') | Some(b'\t') | Some(b'\n') | Some(b'\r') => {
                    self.bump();
                }
                Some(b';') => {
                    while let Some(b) = self.peek() {
                        if b == b'\n' { break; }
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
            Some(b'(') => { self.bump(); Ok(at) }
            Some(b) => Err(SchemaParseError::UnexpectedToken {
                found: (b as char).to_string(),
                expected,
                at,
            }),
            None => Err(SchemaParseError::UnexpectedEof { expected, at }),
        }
    }

    fn expect_rparen(&mut self, open_at: ParseLoc) -> Result<(), SchemaParseError> {
        self.skip_ws_and_comments();
        match self.peek() {
            Some(b')') => { self.bump(); Ok(()) }
            Some(_) | None => Err(SchemaParseError::UnclosedParen { opened_at: open_at }),
        }
    }

    fn parse_ident(&mut self) -> Result<(String, ParseLoc), SchemaParseError> {
        self.skip_ws_and_comments();
        let at = self.loc();
        let start = self.pos;
        match self.peek() {
            Some(b) if b.is_ascii_alphabetic() || b == b'_' => { self.bump(); }
            Some(b) => return Err(SchemaParseError::UnexpectedToken {
                found: (b as char).to_string(),
                expected: "identifier",
                at,
            }),
            None => return Err(SchemaParseError::UnexpectedEof {
                expected: "identifier",
                at,
            }),
        }
        while let Some(b) = self.peek() {
            if b.is_ascii_alphanumeric() || b == b'_' {
                self.bump();
            } else {
                break;
            }
        }
        let ident = std::str::from_utf8(&self.src[start..self.pos])
            .expect("ASCII identifier is UTF-8")
            .to_string();
        Ok((ident, at))
    }

    fn parse_upper_ident(&mut self, what: &'static str) -> Result<(String, ParseLoc), SchemaParseError> {
        let (ident, at) = self.parse_ident()?;
        if !ident.chars().next().map(|c| c.is_ascii_uppercase()).unwrap_or(false) {
            return Err(SchemaParseError::InvalidIdentifier {
                found: ident,
                at,
                reason: what,
            });
        }
        Ok((ident, at))
    }

    fn parse_lower_ident(&mut self) -> Result<(String, ParseLoc), SchemaParseError> {
        let (ident, at) = self.parse_ident()?;
        if !ident.chars().next().map(|c| c.is_ascii_lowercase() || c == '_').unwrap_or(false) {
            return Err(SchemaParseError::InvalidIdentifier {
                found: ident,
                at,
                reason: "field name must start with lowercase letter or underscore",
            });
        }
        Ok((ident, at))
    }

    /// Parse one `(type-name product-or-sum)` declaration. Returns the
    /// parsed TypeShape + the location of its opening paren (for
    /// duplicate-name diagnostics).
    fn parse_type_decl(
        &mut self,
        _decl_locs: &HashMap<String, ParseLoc>,
    ) -> Result<(TypeShape, ParseLoc), SchemaParseError> {
        let open_at = self.expect_lparen("'(' starting a type declaration")?;
        let (type_name, name_at) = self.parse_upper_ident("type name must be UpperCamel")?;

        // Reject reserved CL wrapper names as user-declared types.
        if is_reserved_cl_name(&type_name) {
            return Err(SchemaParseError::ReservedTypeName { name: type_name, at: name_at });
        }

        let variants = self.parse_product_or_sum(&type_name)?;
        self.expect_rparen(open_at)?;
        Ok((TypeShape { name: type_name, variants }, open_at))
    }

    fn parse_product_or_sum(
        &mut self,
        type_name: &str,
    ) -> Result<Vec<Variant>, SchemaParseError> {
        self.skip_ws_and_comments();
        let at = self.loc();
        match self.peek() {
            // A `(` here means either the product field-list `((CLInt x) ...)`
            // or a data variant clause `(VariantName ((...)))`. We
            // disambiguate by peeking ahead — if the first inner token is
            // an identifier whose first byte is uppercase, it's a variant
            // clause (start of sum); if it's `(` it's a product field-spec.
            Some(b'(') => {
                let inner_kind = self.peek_inner_kind(at)?;
                match inner_kind {
                    InnerKind::Variant => {
                        // Sum: one or more variant clauses (parens or bare names)
                        let mut variants = Vec::new();
                        while !self.at_close_paren() {
                            variants.push(self.parse_variant_clause()?);
                            self.skip_ws_and_comments();
                        }
                        Ok(variants)
                    }
                    InnerKind::FieldList => {
                        // Product: parse the single field-list
                        let fields = self.parse_field_list()?;
                        Ok(vec![Variant { name: type_name.to_string(), fields }])
                    }
                }
            }
            // A bare identifier here means a nullary sum variant clause
            // (start of a sum type with nullary first variant).
            Some(b) if (b as char).is_ascii_alphabetic() || b == b'_' => {
                let mut variants = Vec::new();
                while !self.at_close_paren() {
                    variants.push(self.parse_variant_clause()?);
                    self.skip_ws_and_comments();
                }
                Ok(variants)
            }
            Some(b) => Err(SchemaParseError::UnexpectedToken {
                found: (b as char).to_string(),
                expected: "product field-list or sum variant-clause",
                at,
            }),
            None => Err(SchemaParseError::UnexpectedEof {
                expected: "product field-list or sum variant-clause",
                at,
            }),
        }
    }

    fn at_close_paren(&mut self) -> bool {
        self.skip_ws_and_comments();
        matches!(self.peek(), Some(b')'))
    }

    /// Look at the contents of the next `(...)` form (already at the
    /// opening paren) to decide whether it's a field-spec list (product
    /// shape — first inner token is also `(`) or a variant clause (sum
    /// shape — first inner token is an identifier).
    fn peek_inner_kind(&self, at: ParseLoc) -> Result<InnerKind, SchemaParseError> {
        let mut pos = self.pos + 1; // skip the opening '('
        while pos < self.src.len() {
            let b = self.src[pos];
            if b == b' ' || b == b'\t' || b == b'\n' || b == b'\r' {
                pos += 1;
                continue;
            }
            if b == b';' {
                while pos < self.src.len() && self.src[pos] != b'\n' { pos += 1; }
                continue;
            }
            if b == b'(' {
                return Ok(InnerKind::FieldList);
            }
            if b.is_ascii_alphabetic() || b == b'_' {
                return Ok(InnerKind::Variant);
            }
            if b == b')' {
                // `()` as the only inner form means an empty product
                // field-list `(MarkerOnly ())` — a valid tag-only product
                // per design §1.7. We treat this as a field-list shape.
                return Ok(InnerKind::FieldList);
            }
            return Err(SchemaParseError::UnexpectedToken {
                found: (b as char).to_string(),
                expected: "field-spec '(' or variant identifier",
                at,
            });
        }
        Err(SchemaParseError::UnexpectedEof {
            expected: "field-spec or variant identifier",
            at,
        })
    }

    fn parse_field_list(&mut self) -> Result<Vec<Field>, SchemaParseError> {
        let open_at = self.expect_lparen("'(' starting a field list")?;
        let mut fields = Vec::new();
        loop {
            self.skip_ws_and_comments();
            if let Some(b')') = self.peek() {
                self.bump();
                break;
            }
            fields.push(self.parse_field_spec()?);
            if self.at_eof() {
                return Err(SchemaParseError::UnclosedParen { opened_at: open_at });
            }
        }
        Ok(fields)
    }

    fn parse_field_spec(&mut self) -> Result<Field, SchemaParseError> {
        let open_at = self.expect_lparen("'(' starting a field-spec '(field-type field-name)'")?;
        let (type_ident, type_at) = self.parse_upper_ident("field type must be UpperCamel")?;
        let (field_name, _name_at) = self.parse_lower_ident()?;
        self.expect_rparen(open_at)?;
        let field_type = resolve_field_type(&type_ident, type_at)?;
        Ok(Field { name: field_name, field_type })
    }

    fn parse_variant_clause(&mut self) -> Result<Variant, SchemaParseError> {
        self.skip_ws_and_comments();
        let at = self.loc();
        match self.peek() {
            // Data variant: (VariantName (field-list))
            Some(b'(') => {
                let open_at = self.expect_lparen("'(' starting a data variant clause")?;
                let (variant_name, _name_at) = self.parse_upper_ident("variant name must be UpperCamel")?;
                let fields = self.parse_field_list()?;
                self.expect_rparen(open_at)?;
                Ok(Variant { name: variant_name, fields })
            }
            // Nullary variant: bare identifier
            Some(b) if (b as char).is_ascii_alphabetic() || b == b'_' => {
                let (variant_name, _name_at) = self.parse_upper_ident("variant name must be UpperCamel")?;
                Ok(Variant { name: variant_name, fields: Vec::new() })
            }
            Some(b) => Err(SchemaParseError::UnexpectedToken {
                found: (b as char).to_string(),
                expected: "variant clause",
                at,
            }),
            None => Err(SchemaParseError::UnexpectedEof {
                expected: "variant clause",
                at,
            }),
        }
    }
}

enum InnerKind {
    FieldList,
    Variant,
}

fn is_reserved_cl_name(name: &str) -> bool {
    matches!(name, "CLInt" | "CLBool" | "CLFloat" | "CLString" | "CLIO")
}

fn resolve_field_type(name: &str, at: ParseLoc) -> Result<FieldType, SchemaParseError> {
    match name {
        "CLInt" => Ok(FieldType::CLInt),
        "CLBool" => Ok(FieldType::CLBool),
        "CLFloat" => Ok(FieldType::CLFloat),
        "CLString" => Ok(FieldType::CLString),
        "CLIO" => Err(SchemaParseError::ReservedFieldTypeNotYetSupported {
            name: "CLIO",
            at,
        }),
        // Any other UpperCamel name: treat as a forward/back ADT reference;
        // resolution validates in pass 2.
        other => Ok(FieldType::Adt(other.to_string())),
    }
}

// ---------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // T1 — Schema parser — well-formed product type
    // spec: design/platform/sprint71-redesign.md §1 + tests/plan/sprint71-platform.md row T1
    #[test]
    fn t1_well_formed_product() {
        let s = Schema::parse("((Rectangle ((CLInt w) (CLInt h))))").unwrap();
        let r = s.lookup_type("Rectangle").expect("Rectangle declared");
        assert_eq!(r.variants.len(), 1, "product is a single-variant shape");
        let v = &r.variants[0];
        assert_eq!(v.fields.len(), 2);
        assert_eq!(v.fields[0].name, "w");
        assert_eq!(v.fields[0].field_type, FieldType::CLInt);
        assert_eq!(v.fields[1].name, "h");
        assert_eq!(v.fields[1].field_type, FieldType::CLInt);
    }

    // T2 — Schema parser — well-formed sum type
    // spec: design/platform/sprint71-redesign.md §1 + tests/plan/sprint71-platform.md row T2
    #[test]
    fn t2_well_formed_sum() {
        let s = Schema::parse("((OptionInt None (Some ((CLInt val)))))").unwrap();
        let o = s.lookup_type("OptionInt").expect("OptionInt declared");
        assert_eq!(o.variants.len(), 2);
        assert_eq!(o.variants[0].name, "None");
        assert!(o.variants[0].fields.is_empty(), "None is nullary");
        assert_eq!(o.variants[1].name, "Some");
        assert_eq!(o.variants[1].fields.len(), 1);
        assert_eq!(o.variants[1].fields[0].name, "val");
        assert_eq!(o.variants[1].fields[0].field_type, FieldType::CLInt);
    }

    // T3 — Schema parser — recursive sum (ListInt self-reference)
    // spec: design/platform/sprint71-redesign.md §1.4
    #[test]
    fn t3_recursive_sum_listint() {
        let s = Schema::parse("((ListInt Nil (Cons ((CLInt head) (ListInt tail)))))").unwrap();
        let l = s.lookup_type("ListInt").expect("ListInt declared");
        assert_eq!(l.variants.len(), 2);
        let cons = l.variants.iter().find(|v| v.name == "Cons").unwrap();
        assert_eq!(cons.fields.len(), 2);
        assert_eq!(cons.fields[0].field_type, FieldType::CLInt);
        // The `tail` field self-references ListInt.
        assert_eq!(cons.fields[1].name, "tail");
        match &cons.fields[1].field_type {
            FieldType::Adt(name) => assert_eq!(name, "ListInt"),
            other => panic!("expected Adt(ListInt), got {other:?}"),
        }
    }

    // T4 — Schema parser — nested product (Bounds → Point)
    // spec: tests/plan/sprint71-platform.md row T4
    #[test]
    fn t4_nested_product_bounds_point() {
        let s = Schema::parse(
            "((Point ((CLInt x) (CLInt y))) (Bounds ((Point tl) (Point br))))"
        ).unwrap();
        assert!(s.lookup_type("Point").is_some());
        let b = s.lookup_type("Bounds").unwrap();
        assert_eq!(b.variants[0].fields[0].field_type, FieldType::Adt("Point".to_string()));
        assert_eq!(b.variants[0].fields[1].field_type, FieldType::Adt("Point".to_string()));
    }

    // T5 — Schema parser — polymorphic-instantiated naming convention
    // spec: design/platform/sprint71-redesign.md §1.3
    #[test]
    fn t5_polymorphic_instantiation_distinct_types() {
        let s = Schema::parse(
            "((OptionInt None (Some ((CLInt val)))) \
             (OptionString None (Some ((CLString val)))))"
        ).unwrap();
        let oi = s.lookup_type("OptionInt").unwrap();
        let os = s.lookup_type("OptionString").unwrap();
        assert_eq!(oi.variants[1].fields[0].field_type, FieldType::CLInt);
        assert_eq!(os.variants[1].fields[0].field_type, FieldType::CLString);
    }

    // T6 — Schema parser — malformed schema yields position-tagged error
    // spec: design/platform/sprint71-redesign.md §1.7
    #[test]
    fn t6_malformed_missing_close_paren_position_tagged() {
        let res = Schema::parse("((Rectangle ((CLInt w (CLInt h))))");
        let err = res.expect_err("missing close-paren should fail");
        // Every error carries a ParseLoc.
        match err {
            SchemaParseError::UnclosedParen { opened_at }
            | SchemaParseError::UnexpectedEof { at: opened_at, .. }
            | SchemaParseError::UnexpectedToken { at: opened_at, .. } => {
                assert!(opened_at.offset > 0, "position past column 0");
            }
            other => panic!("expected position-tagged err; got {other:?}"),
        }
    }

    // T7 — Schema parser — reserved field-type name conflict
    // spec: design/platform/sprint71-redesign.md §1.2
    #[test]
    fn t7_reserved_type_name_rejected() {
        let res = Schema::parse("((CLInt ((CLInt foo))))");
        let err = res.expect_err("redefining CLInt should fail");
        match err {
            SchemaParseError::ReservedTypeName { name, .. } => assert_eq!(name, "CLInt"),
            other => panic!("expected ReservedTypeName, got {other:?}"),
        }
    }

    // T8 — Schema parser — offset computation matches layout rule
    // spec: design/platform/sprint71-redesign.md §3 + tests/plan/sprint71-platform.md row T8
    #[test]
    fn t8_offset_computation_matches_layout() {
        let s = Schema::parse("((Rectangle ((CLInt w) (CLInt h))))").unwrap();
        // Tag at offset 0 (4 bytes) + 4 bytes pad → first field at 8.
        assert_eq!(s.lookup_field_offset("Rectangle", "w"), Some(8));
        assert_eq!(s.lookup_field_offset("Rectangle", "h"), Some(16));
        // Dot-qualified form is also accepted on products.
        assert_eq!(s.lookup_field_offset("Rectangle", "Rectangle.w"), Some(8));
    }

    // CLIO is reserved-but-not-supported per §1.2.
    #[test]
    fn clio_field_type_rejected_with_reserved_for_future_error() {
        let res = Schema::parse("((Foo ((CLIO io))))");
        let err = res.expect_err("CLIO as field type must be rejected");
        match err {
            SchemaParseError::ReservedFieldTypeNotYetSupported { name, .. } => {
                assert_eq!(name, "CLIO");
            }
            other => panic!("expected ReservedFieldTypeNotYetSupported, got {other:?}"),
        }
    }

    // CLIO is also rejected as a top-level type-decl name.
    #[test]
    fn clio_top_level_type_decl_rejected_as_reserved() {
        let res = Schema::parse("((CLIO ((CLInt foo))))");
        match res.expect_err("redefining CLIO should fail") {
            SchemaParseError::ReservedTypeName { name, .. } => assert_eq!(name, "CLIO"),
            other => panic!("expected ReservedTypeName, got {other:?}"),
        }
    }

    // Duplicate type names rejected.
    #[test]
    fn duplicate_type_name_rejected_with_both_locs() {
        let res = Schema::parse("((Foo ((CLInt a))) (Foo ((CLInt b))))");
        match res.expect_err("duplicate type should fail") {
            SchemaParseError::DuplicateTypeName { name, at, first_at } => {
                assert_eq!(name, "Foo");
                assert!(at.offset > first_at.offset);
            }
            other => panic!("expected DuplicateTypeName, got {other:?}"),
        }
    }

    // Unknown field type (forward-ref to a non-declared name).
    #[test]
    fn unknown_field_type_rejected() {
        let res = Schema::parse("((Foo ((Bar b))))");
        match res.expect_err("unknown field type should fail") {
            SchemaParseError::UnknownFieldType { name, .. } => assert_eq!(name, "Bar"),
            other => panic!("expected UnknownFieldType, got {other:?}"),
        }
    }

    // Empty schema parses to an empty Schema per §1.7.
    #[test]
    fn empty_schema_parses_to_empty() {
        let s = Schema::parse("").unwrap();
        assert!(s.is_empty());
        let s2 = Schema::parse("  ;; just a comment\n").unwrap();
        assert!(s2.is_empty());
    }

    // Empty product `(MarkerOnly ())` parses to a tag-only type.
    #[test]
    fn empty_product_marker_only() {
        let s = Schema::parse("((MarkerOnly ()))").unwrap();
        let m = s.lookup_type("MarkerOnly").unwrap();
        assert_eq!(m.variants.len(), 1);
        assert!(m.variants[0].fields.is_empty());
    }

    // Sum-type variant field offset lookup.
    #[test]
    fn sum_variant_field_offset_lookup() {
        let s = Schema::parse("((OptionInt None (Some ((CLInt val)))))").unwrap();
        // Some.val is the first field of the Some variant (offset 8).
        assert_eq!(
            s.lookup_variant_field_offset("OptionInt", "Some", "val"),
            Some(8)
        );
        // Non-existent variant or field returns None.
        assert!(s.lookup_variant_field_offset("OptionInt", "None", "val").is_none());
        assert!(s.lookup_variant_field_offset("OptionInt", "Some", "nope").is_none());
    }

    // Field-type lookup helps the type-witness check.
    #[test]
    fn lookup_field_type_helper() {
        let s = Schema::parse("((Rectangle ((CLInt w) (CLInt h))))").unwrap();
        assert_eq!(s.lookup_field_type("Rectangle", None, "w"), Some(&FieldType::CLInt));
        let s2 = Schema::parse("((OptionInt None (Some ((CLInt val)))))").unwrap();
        assert_eq!(
            s2.lookup_field_type("OptionInt", Some("Some"), "val"),
            Some(&FieldType::CLInt)
        );
    }

    // Variant names accessor.
    #[test]
    fn variant_names_accessor() {
        let s = Schema::parse("((OptionInt None (Some ((CLInt val)))))").unwrap();
        let names = s.variant_names("OptionInt").unwrap();
        assert_eq!(names, vec!["None", "Some"]);
    }

    // Line comments work.
    #[test]
    fn line_comments_are_skipped() {
        let s = Schema::parse(
            "; leading comment\n\
             ((Rectangle ; trailing\n\
                ((CLInt w) ; w is width\n\
                 (CLInt h))))"
        ).unwrap();
        assert!(s.lookup_type("Rectangle").is_some());
    }
}
