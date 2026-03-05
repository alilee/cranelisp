use serde::{Deserialize, Serialize};
use std::path::PathBuf;

use crate::Span;

/// All errors carry a Span for source location.
#[derive(Debug)]
pub enum CranelispError {
    ParseError {
        message: String,
        span: Span,
    },
    TypeError {
        message: String,
        span: Span,
    },
    CodegenError {
        message: String,
        span: Span,
    },
    ModuleError {
        message: String,
        file: Option<PathBuf>,
        span: Span,
    },
}

impl CranelispError {
    pub fn span(&self) -> Span {
        match self {
            CranelispError::ParseError { span, .. }
            | CranelispError::TypeError { span, .. }
            | CranelispError::CodegenError { span, .. }
            | CranelispError::ModuleError { span, .. } => *span,
        }
    }

    pub fn message(&self) -> &str {
        match self {
            CranelispError::ParseError { message, .. }
            | CranelispError::TypeError { message, .. }
            | CranelispError::CodegenError { message, .. }
            | CranelispError::ModuleError { message, .. } => message,
        }
    }
}

impl std::fmt::Display for CranelispError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CranelispError::ParseError { message, span } => {
                write!(f, "parse error at {span}: {message}")
            }
            CranelispError::TypeError { message, span } => {
                write!(f, "type error at {span}: {message}")
            }
            CranelispError::CodegenError { message, span } => {
                write!(f, "codegen error at {span}: {message}")
            }
            CranelispError::ModuleError {
                message,
                file,
                span,
            } => {
                if let Some(path) = file {
                    write!(f, "module error in {}: at {span}: {message}", path.display())
                } else {
                    write!(f, "module error at {span}: {message}")
                }
            }
        }
    }
}

impl std::error::Error for CranelispError {}

/// Non-fatal diagnostic accumulated during compilation.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Warning {
    pub message: String,
    pub span: Span,
}
