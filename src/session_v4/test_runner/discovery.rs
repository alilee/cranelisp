//! The one eligibility scan (`design/int/test-runner.md` §5): which `test-`
//! definitions of a module run. `/run-tests`, `/run-all-tests`, `--test` and
//! the `discover-tests` extern all list tests through [`scan_modules`];
//! `/tests-for` filters its referers through the same
//! [`classify_test_definition`].

use cranelisp_types::{
    Binding, Callable, FQSymbol, Life, ModuleFullPath, Scheme, Span, TemplateBody, Type, Warning,
    WarningKind,
};

use crate::code::{Code, SessionSymbolTable};

const TEST_PREFIX: &str = "test-";

/// The tests the scan admits, in FQ-name order, and one warning per `test-`
/// definition it excluded for its type.
#[derive(Debug, Default)]
pub(crate) struct Discovery {
    pub(crate) tests: Vec<FQSymbol>,
    pub(crate) warnings: Vec<Warning>,
}

/// Scan every module in `modules`. A module without a table contributes
/// nothing.
pub(crate) fn scan_modules(
    tables: &dashmap::DashMap<ModuleFullPath, SessionSymbolTable>,
    modules: &[ModuleFullPath],
) -> Discovery {
    let mut discovery = Discovery::default();
    for module in modules {
        if let Some(table) = tables.get(module) {
            scan_table(&table, &mut discovery);
        }
    }
    discovery.tests.sort_by_cached_key(ToString::to_string);
    discovery
}

/// How a callable definition named `test-…` stands under the test signature
/// (REPL §16.1).
pub(crate) enum TestDefinition<'e> {
    /// Its scheme is exactly `(Fn [] (Option String))`: it is a test.
    Test,
    /// Any other scheme: not a test, and the runner warns.
    Mistyped(&'e Callable<Code>),
}

/// The one definition of a test function. `None` when the binding is not a
/// `test-` callable definition at all: another name, an internal listing
/// entry, or a non-callable declaration.
pub(crate) fn classify_test_definition<'e>(
    name: &str,
    entry: &'e Binding<Code>,
) -> Option<TestDefinition<'e>> {
    if !name.starts_with(TEST_PREFIX) || crate::worker::is_internal_listing_entry(name, entry) {
        return None;
    }
    let callable = entry.callable()?;
    Some(if is_test_scheme(&callable.arm.scheme) {
        TestDefinition::Test
    } else {
        TestDefinition::Mistyped(callable)
    })
}

/// Every test defined in `table`, and one warning per mistyped `test-`
/// definition. Imported names are not definitions of this table, so a test is
/// listed once, under its home module.
fn scan_table(table: &SessionSymbolTable, discovery: &mut Discovery) {
    for (name, entry) in table.all_symbols() {
        let Some(definition) = classify_test_definition(name.as_ref(), entry) else {
            continue;
        };
        let id = FQSymbol {
            module: table.path.clone(),
            symbol: name.clone(),
        };
        match definition {
            TestDefinition::Test => discovery.tests.push(id),
            TestDefinition::Mistyped(callable) => discovery.warnings.push(Warning {
                kind: WarningKind::Other,
                message: format!(
                    "`{id}` is not run as a test: its type is `{}`, and a test must have \
                     type `(Fn [] (Option String))`",
                    callable.arm.scheme.ty
                ),
                span: definition_span(&callable.arm.life),
            }),
        }
    }
}

/// The exact test scheme. It is a soundness condition, not a preference: the
/// runner decodes the returned word as an `(Option String)`.
fn is_test_scheme(scheme: &Scheme) -> bool {
    let Type::Fn(params, ret) = &scheme.ty else {
        return false;
    };
    let Type::ADT(name, args) = ret.as_ref() else {
        return false;
    };
    params.is_empty()
        && name.name.as_ref() == "Option"
        && name.module.as_ref() == "primitives"
        && matches!(args.as_slice(), [Type::String])
}

fn definition_span<C: cranelisp_types::CodeStore>(life: &Life<C>) -> Span {
    match life {
        Life::Concrete {
            ast: Some(variant), ..
        }
        | Life::Template {
            body: TemplateBody::Ast(variant),
            ..
        } => variant.span,
        _ => Span::SYNTHETIC,
    }
}

#[cfg(test)]
mod tests;
