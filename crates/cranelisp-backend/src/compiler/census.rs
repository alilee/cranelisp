//! The category census (`design/backend/non-concrete-release-contract.md`
//! §7.3): a count of every point at which codegen emits, or silently skips, an
//! RC operation on a word whose heap category it cannot name, and of every
//! constructor field read, keyed by the frame being compiled. Each codegen
//! target also records one frame, the denominator a zero reading is read
//! against.
//!
//! Debug builds only. In a release build [`record`] neither builds its record
//! nor keeps a tally, and the environment variable is never read. Every record
//! point is host code, so emitted CLIF does not depend on the census. Nothing
//! here writes to a standard stream: the in-process tally is read by unit
//! tests, and `CRANELISP_CATEGORY_CENSUS=<path>` appends one line per reported
//! record to that file, so a suite run aggregates across every process it
//! spawns.

use cranelisp_types::{CallableOrigin, CodeStore, Decl, ModuleFullPath, Symbol, Type};

/// The requesting frame's origin, as the census partitions it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum Partition {
    Ctor,
    Accessor,
    TraitMethod,
    Plain,
}

impl Partition {
    /// The partition of the binding a codegen target belongs to. An
    /// overloaded or macro binding, or a target with no binding, is `Plain`.
    pub(crate) fn of<C: CodeStore>(declaration: Option<&Decl<C>>) -> Self {
        let Some(Decl::Callable(callable)) = declaration else {
            return Partition::Plain;
        };
        match callable.origin {
            CallableOrigin::Ctor { .. } => Partition::Ctor,
            CallableOrigin::Accessor { .. } => Partition::Accessor,
            CallableOrigin::TraitMethod { .. } => Partition::TraitMethod,
            CallableOrigin::Plain
            | CallableOrigin::RustPrimitive
            | CallableOrigin::PlatformEffect { .. } => Partition::Plain,
        }
    }

    #[cfg(debug_assertions)]
    fn name(self) -> &'static str {
        match self {
            Partition::Ctor => "Ctor",
            Partition::Accessor => "Accessor",
            Partition::TraitMethod => "TraitMethod",
            Partition::Plain => "Plain",
        }
    }
}

/// The outermost shape of a type that is not concrete.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum Shape {
    /// A bare type variable.
    Var,
    /// A named ADT with a residual argument somewhere inside it.
    Adt,
    /// A function type with a residual parameter or result.
    Fn,
    /// An unresolved higher-kinded head.
    Hkt,
}

impl Shape {
    /// The shape of `ty`, which the caller has found not concrete. A scalar is
    /// always concrete, so it has no shape.
    pub(crate) fn of_residual(ty: &Type) -> Self {
        match ty {
            Type::Var(_) => Shape::Var,
            Type::ADT(..) => Shape::Adt,
            Type::Fn(..) => Shape::Fn,
            Type::TyConApp(..) => Shape::Hkt,
            Type::Int | Type::Bool | Type::String | Type::Float => {
                unreachable!("census: a scalar type is concrete and has no residual shape")
            }
        }
    }

    #[cfg(debug_assertions)]
    fn name(self) -> &'static str {
        match self {
            Shape::Var => "var",
            Shape::Adt => "adt",
            Shape::Fn => "fn",
            Shape::Hkt => "hkt",
        }
    }
}

/// The instantiation at which a constructor's field types were read.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum FieldClass {
    /// The declaration has no parameters, or the scrutinee supplies one
    /// concrete argument per parameter.
    Concrete,
    /// The argument count matches and at least one argument is not concrete.
    Residual,
    /// The declaration is parametric and the scrutinee supplies no argument
    /// list of that length, including no scrutinee type at all.
    Absent,
}

impl FieldClass {
    /// Classify a read of a declaration with `type_params` parameters at
    /// `scrutinee`, before any substitution.
    pub(crate) fn of(type_params: usize, scrutinee: Option<&Type>) -> Self {
        if type_params == 0 {
            return FieldClass::Concrete;
        }
        match scrutinee {
            Some(Type::ADT(_, args)) if args.len() == type_params => {
                if args
                    .iter()
                    .all(|arg| cranelisp_types::ConcreteType::from_type(arg).is_ok())
                {
                    FieldClass::Concrete
                } else {
                    FieldClass::Residual
                }
            }
            _ => FieldClass::Absent,
        }
    }

    #[cfg(debug_assertions)]
    fn name(self) -> &'static str {
        match self {
            FieldClass::Concrete => "concrete",
            FieldClass::Residual => "residual",
            FieldClass::Absent => "absent",
        }
    }
}

/// Whether a constructor's scheme supplies a type for each of its fields.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum Declaration {
    Full,
    /// Fewer field types than fields; the read refuses the constructor.
    Short,
}

impl Declaration {
    #[cfg(debug_assertions)]
    fn name(self) -> &'static str {
        match self {
            Declaration::Full => "full",
            Declaration::Short => "short",
        }
    }
}

/// One observation at a record point.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum Record {
    /// A residual type licensed as `Mixed` by `signature_heap_category`.
    Retain(Shape),
    /// A residual-typed value released by the shallow guarded decrement.
    Release(Shape),
    /// A parameter introduced with no type.
    Absent,
    /// A constructor's field types read by the match lowering.
    Field {
        class: FieldClass,
        declaration: Declaration,
    },
    /// One codegen target compiled under the census.
    Frame,
}

#[cfg(debug_assertions)]
impl Record {
    /// Whether the record is written to the census file. A concrete read of a
    /// fully declared constructor is counted in the tally only.
    fn reported(self) -> bool {
        !matches!(
            self,
            Record::Field {
                class: FieldClass::Concrete,
                declaration: Declaration::Full,
            }
        )
    }

    /// The point, shape and class columns of the record's line.
    fn columns(self) -> [&'static str; 3] {
        match self {
            Record::Retain(shape) => ["retain", shape.name(), "-"],
            Record::Release(shape) => ["release", shape.name(), "-"],
            Record::Absent => ["absent", "absent", "-"],
            Record::Field { class, declaration } => ["field", declaration.name(), class.name()],
            Record::Frame => ["frame", "-", "-"],
        }
    }
}

/// The frame a record is attributed to: the codegen target being compiled,
/// inherited by every inner compiler of that target.
#[derive(Clone, Debug)]
pub(crate) struct Frame {
    #[cfg(debug_assertions)]
    partition: Partition,
    #[cfg(debug_assertions)]
    owner: String,
}

impl Frame {
    pub(crate) fn new(partition: Partition, module: &ModuleFullPath, symbol: &Symbol) -> Self {
        #[cfg(not(debug_assertions))]
        let _ = (partition, module, symbol);
        Frame {
            #[cfg(debug_assertions)]
            partition,
            #[cfg(debug_assertions)]
            owner: format!("{module}/{symbol}"),
        }
    }

    /// The frame for codegen target `symbol` of `module`, whose binding
    /// carries `declaration`. Selecting the target records its frame.
    pub(crate) fn of_target<C: CodeStore>(
        declaration: Option<&Decl<C>>,
        module: &ModuleFullPath,
        symbol: &Symbol,
    ) -> Self {
        let frame = Frame::new(Partition::of(declaration), module, symbol);
        record(&frame, || Record::Frame);
        frame
    }

    /// A `Plain` frame for a fixture that builds a compiler by hand.
    #[cfg(test)]
    pub(crate) fn for_test() -> Self {
        Frame::new(
            Partition::Plain,
            &ModuleFullPath::from("test"),
            &Symbol::from("fixture"),
        )
    }
}

/// Count the record `observe` builds against `frame`. A release build never
/// calls `observe`, so no classification work runs outside the census.
#[inline]
pub(crate) fn record(frame: &Frame, observe: impl FnOnce() -> Record) {
    #[cfg(debug_assertions)]
    sink::record(frame, observe());
    #[cfg(not(debug_assertions))]
    let _ = (frame, observe);
}

#[cfg(debug_assertions)]
mod sink {
    use std::collections::BTreeMap;
    use std::fs::File;
    use std::io::Write;
    use std::sync::{LazyLock, Mutex};

    use super::{Frame, Partition, Record};

    type Key = (String, Partition, Record);

    static TALLY: LazyLock<Mutex<BTreeMap<Key, u64>>> =
        LazyLock::new(|| Mutex::new(BTreeMap::new()));

    /// The census file, opened once for appending. A path that cannot be
    /// opened is a misconfigured measurement and stops the process rather
    /// than reading as zero traffic.
    static FILE: LazyLock<Option<Mutex<File>>> = LazyLock::new(|| {
        let path = std::env::var_os("CRANELISP_CATEGORY_CENSUS")?;
        let file = std::fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(&path)
            .unwrap_or_else(|error| {
                panic!("CRANELISP_CATEGORY_CENSUS: cannot open {path:?} for appending: {error}")
            });
        Some(Mutex::new(file))
    });

    pub(super) fn record(frame: &Frame, record: Record) {
        let key = (frame.owner.clone(), frame.partition, record);
        *TALLY
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .entry(key)
            .or_default() += 1;
        if record.reported()
            && let Some(file) = FILE.as_ref()
        {
            let [point, shape, class] = record.columns();
            // One `write` per line, so O_APPEND keeps concurrent writers'
            // lines whole.
            let line = format!(
                "{point}\t{}\t{shape}\t{class}\t{}\n",
                frame.partition.name(),
                frame.owner
            );
            file.lock()
                .unwrap_or_else(|poisoned| poisoned.into_inner())
                .write_all(line.as_bytes())
                .unwrap_or_else(|error| panic!("CRANELISP_CATEGORY_CENSUS: write failed: {error}"));
        }
    }

    /// This process's records against the frame named `owner`
    /// (`module/symbol`), as `point partition shape class` → count.
    #[cfg(test)]
    pub(crate) fn tally(owner: &str) -> BTreeMap<String, u64> {
        TALLY
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .iter()
            .filter(|((frame, ..), _)| frame == owner)
            .map(|((_, partition, record), count)| {
                let [point, shape, class] = record.columns();
                (
                    format!("{point} {} {shape} {class}", partition.name()),
                    *count,
                )
            })
            .collect()
    }
}

#[cfg(all(test, debug_assertions))]
pub(crate) use sink::tally;

#[cfg(all(test, debug_assertions))]
mod tests;
