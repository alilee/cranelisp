//! The runtime's switches: the crate's only reader of its configuration.
//!
//! A linked executable bakes the switch values effective at `--link`: the
//! compiler calls [`capture_runtime_switches`] and embeds the opaque bytes in
//! the startup object, and the startup stub passes them to
//! [`cranelisp_install_runtime_switches`] as its first call. The runtime then
//! answers only from that capture and never reads its launch environment.
//! Without an install (the compiler process) the switches come from the
//! process environment.

use std::sync::OnceLock;

use crate::panic::{Fault, terminate};

macro_rules! switches {
    ($($member:ident => $name:literal,)*) => {
        /// The closed set of runtime switches.
        #[derive(Debug, Clone, Copy, PartialEq, Eq)]
        pub(crate) enum Switch {
            $($member,)*
        }

        impl Switch {
            pub(crate) const ALL: [Switch; [$($name),*].len()] = [$(Switch::$member,)*];

            pub(crate) const fn name(self) -> &'static str {
                match self {
                    $(Switch::$member => $name,)*
                }
            }
        }
    };
}

switches! {
    HeapScan => "CRANELISP_HEAP_SCAN",
    RcTrace => "CRANELISP_RC_TRACE",
    NonatomicRc => "CRANELISP_NONATOMIC_RC",
    RcStats => "CRANELISP_RC_STATS",
    QuarantineFreed => "CRANELISP_QUARANTINE_FREED",
    QuarantineMaxBytes => "CRANELISP_QUARANTINE_MAX_BYTES",
    ScrubFreed => "CRANELISP_SCRUB_FREED",
    AllocParity => "CRANELISP_ALLOC_PARITY",
    AllocParityDump => "CRANELISP_ALLOC_PARITY_DUMP",
    RcDecCheck => "CRANELISP_RC_DEC_CHECK",
    TestFaults => "CRANELISP_TEST_FAULTS",
    TestFault => "CRANELISP_TEST_FAULT",
    SparkStats => "CRANELISP_SPARK_STATS",
    IvarSpin => "CRANELISP_IVAR_SPIN",
    SaturationGate => "CRANELISP_SATURATION_GATE",
    SparkCoreMult => "CRANELISP_SPARK_CORE_MULT",
    SparkBudget => "CRANELISP_SPARK_BUDGET",
    SparkMaxDepth => "CRANELISP_SPARK_MAX_DEPTH",
    HierDecline => "CRANELISP_HIER_DECLINE",
    DriveMode => "CRANELISP_DRIVE_MODE",
    ReactorBackstopMs => "CRANELISP_REACTOR_BACKSTOP_MS",
    Degree => "CRANELISP_DEGREE",
}

const MEMBER_COUNT: usize = Switch::ALL.len();

/// One value per switch; `None` where the switch is unset.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Values([Option<Box<str>>; MEMBER_COUNT]);

impl Values {
    fn unset() -> Values {
        Values(std::array::from_fn(|_| None))
    }

    /// A value that is not UTF-8 is read lossily: it stays set, and it parses
    /// as no number or word, as a direct read treated it.
    fn from_environment() -> Values {
        Values(
            Switch::ALL
                .map(|switch| std::env::var_os(switch.name()).map(|v| v.to_string_lossy().into())),
        )
    }

    fn get(&self, switch: Switch) -> Option<&str> {
        self.0[switch as usize].as_deref()
    }

    fn set(&mut self, switch: Switch, value: &str) {
        self.0[switch as usize] = Some(value.into());
    }
}

/// The first byte of every capture.
const FORMAT: u8 = 1;

/// The format byte, then for each set member its name and value, each as a
/// little-endian `u32` length followed by UTF-8 bytes.
fn encode(values: &Values) -> Vec<u8> {
    let mut bytes = vec![FORMAT];
    for switch in Switch::ALL {
        if let Some(value) = values.get(switch) {
            for text in [switch.name(), value] {
                bytes.extend_from_slice(&(text.len() as u32).to_le_bytes());
                bytes.extend_from_slice(text.as_bytes());
            }
        }
    }
    bytes
}

/// Why a capture cannot be installed.
#[derive(Debug, PartialEq, Eq)]
enum DecodeError {
    Empty,
    UnknownFormat(u8),
    Truncated,
    NotUtf8,
    UnknownName(String),
    Repeated(Switch),
}

impl std::fmt::Display for DecodeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DecodeError::Empty => write!(f, "the capture is empty"),
            DecodeError::UnknownFormat(b) => write!(f, "unknown capture format {b}"),
            DecodeError::Truncated => write!(f, "the capture is truncated"),
            DecodeError::NotUtf8 => write!(f, "the capture holds text that is not UTF-8"),
            DecodeError::UnknownName(name) => write!(f, "unknown switch `{name}`"),
            DecodeError::Repeated(s) => write!(f, "switch `{}` appears twice", s.name()),
        }
    }
}

fn decode(bytes: &[u8]) -> Result<Values, DecodeError> {
    let (&format, mut rest) = bytes.split_first().ok_or(DecodeError::Empty)?;
    if format != FORMAT {
        return Err(DecodeError::UnknownFormat(format));
    }
    let mut values = Values::unset();
    while !rest.is_empty() {
        let name = take_text(&mut rest)?;
        let switch = Switch::ALL
            .into_iter()
            .find(|s| s.name() == name)
            .ok_or_else(|| DecodeError::UnknownName(name.into()))?;
        let value = take_text(&mut rest)?;
        if values.get(switch).is_some() {
            return Err(DecodeError::Repeated(switch));
        }
        values.set(switch, value);
    }
    Ok(values)
}

fn take_text<'a>(rest: &mut &'a [u8]) -> Result<&'a str, DecodeError> {
    let (len, tail) = rest
        .split_first_chunk::<4>()
        .ok_or(DecodeError::Truncated)?;
    let len = u32::from_le_bytes(*len) as usize;
    if tail.len() < len {
        return Err(DecodeError::Truncated);
    }
    let (text, tail) = tail.split_at(len);
    *rest = tail;
    std::str::from_utf8(text).map_err(|_| DecodeError::NotUtf8)
}

/// Why an install is refused.
#[derive(Debug)]
enum Refusal {
    AlreadyRead,
    Malformed(DecodeError),
    PoolExists(String),
}

impl std::fmt::Display for Refusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Refusal::AlreadyRead => write!(f, "a runtime switch was read before the install"),
            Refusal::Malformed(e) => write!(f, "malformed capture: {e}"),
            Refusal::PoolExists(e) => write!(f, "the worker pool already exists: {e}"),
        }
    }
}

static SNAPSHOT: OnceLock<Values> = OnceLock::new();

fn snapshot() -> &'static Values {
    SNAPSHOT.get_or_init(Values::from_environment)
}

/// The value of `switch`, or `None` when it is unset.
pub(crate) fn value(switch: Switch) -> Option<&'static str> {
    snapshot().get(switch)
}

/// Whether `switch` is set, to any value.
pub(crate) fn is_set(switch: Switch) -> bool {
    value(switch).is_some()
}

/// Capture the current runtime switch values as an opaque byte block.
///
/// The bytes are meaningful only to [`cranelisp_install_runtime_switches`] of
/// the same runtime build. The first capture or switch read fixes the
/// process's own switch values, so it must follow any change to the process
/// environment that should reach the capture.
pub fn capture_runtime_switches() -> Vec<u8> {
    encode(snapshot())
}

fn install(bytes: &[u8]) -> Result<(), Refusal> {
    let values = decode(bytes).map_err(Refusal::Malformed)?;
    SNAPSHOT.set(values).map_err(|_| Refusal::AlreadyRead)?;
    // An explicit count, so `rayon` does not consult `RAYON_NUM_THREADS`.
    let cores = std::thread::available_parallelism().map_or(1, |n| n.get());
    rayon::ThreadPoolBuilder::new()
        .num_threads(cores)
        .build_global()
        .map_err(|e| Refusal::PoolExists(e.to_string()))
}

/// The site a configuration fault names.
const INSTALL_SITE: &str = "cranelisp_install_runtime_switches";

/// Install a capture from [`capture_runtime_switches`] as the runtime's only
/// switch source.
///
/// Must be called before anything else in the runtime, because an allocation
/// already reads a switch. Also builds the worker pool with the machine's
/// core count. Ends the process with a configuration fault if a switch was
/// already read, the worker pool already exists, or the capture is malformed.
///
/// # Safety
///
/// `ptr` must point to `len` readable bytes.
#[unsafe(export_name = "cranelisp_install_runtime_switches")]
#[allow(clippy::not_unsafe_ptr_arg_deref)] // Called from the startup stub; cannot be marked unsafe
pub extern "C" fn cranelisp_install_runtime_switches(ptr: *const u8, len: usize) {
    let bytes: &[u8] = if ptr.is_null() || len == 0 {
        &[]
    } else {
        // SAFETY: the caller guarantees `ptr` points to `len` readable bytes.
        unsafe { std::slice::from_raw_parts(ptr, len) }
    };
    if let Err(refusal) = install(bytes) {
        terminate(Fault::Configuration {
            site: INSTALL_SITE,
            detail: &refusal.to_string(),
        })
    }
}

#[cfg(test)]
mod tests;
