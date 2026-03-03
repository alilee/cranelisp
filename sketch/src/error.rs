use std::fmt;
use std::path::PathBuf;

/// Byte offset range in source text.
pub type Span = (usize, usize);

#[derive(Debug)]
pub enum CranelispError {
    ParseError {
        message: String,
        offset: usize,
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

impl fmt::Display for CranelispError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CranelispError::ParseError { message, offset } => {
                write!(f, "Parse error at offset {}: {}", offset, message)
            }
            CranelispError::TypeError { message, span } => {
                write!(f, "Type error at {}..{}: {}", span.0, span.1, message)
            }
            CranelispError::CodegenError { message, span } => {
                write!(f, "Codegen error at {}..{}: {}", span.0, span.1, message)
            }
            CranelispError::ModuleError { message, file, .. } => {
                if let Some(path) = file {
                    write!(f, "Module error in {}: {}", path.display(), message)
                } else {
                    write!(f, "Module error: {}", message)
                }
            }
        }
    }
}

impl std::error::Error for CranelispError {}

/// Format a CranelispError with source context, showing the offending line and a caret.
pub fn format_error(source: &str, err: &CranelispError) -> String {
    let offset = match err {
        CranelispError::ParseError { offset, .. } => *offset,
        CranelispError::TypeError { span, .. } => span.0,
        CranelispError::CodegenError { span, .. } => span.0,
        CranelispError::ModuleError { span, .. } => span.0,
    };

    let (line_num, col, line_text) = offset_to_line_col(source, offset);
    format!(
        "{}\n  --> {}:{}\n   | {}\n   | {}^",
        err,
        line_num,
        col,
        line_text,
        " ".repeat(col.saturating_sub(1))
    )
}

/// Format a CranelispError with file path and source context.
pub fn format_error_in_file(
    file_path: &std::path::Path,
    source: &str,
    err: &CranelispError,
) -> String {
    let offset = match err {
        CranelispError::ParseError { offset, .. } => *offset,
        CranelispError::TypeError { span, .. } => span.0,
        CranelispError::CodegenError { span, .. } => span.0,
        CranelispError::ModuleError { span, .. } => span.0,
    };

    let (line_num, col, line_text) = offset_to_line_col(source, offset);
    format!(
        "{}\n  --> {}:{}:{}\n   | {}\n   | {}^",
        err,
        file_path.display(),
        line_num,
        col,
        line_text,
        " ".repeat(col.saturating_sub(1))
    )
}

fn offset_to_line_col(source: &str, offset: usize) -> (usize, usize, &str) {
    let mut line_start = 0;
    let mut line_num = 1;
    for (i, ch) in source.char_indices() {
        if i >= offset {
            break;
        }
        if ch == '\n' {
            line_start = i + 1;
            line_num += 1;
        }
    }
    let line_end = source[line_start..]
        .find('\n')
        .map(|i| line_start + i)
        .unwrap_or(source.len());
    let col = offset - line_start + 1;
    (line_num, col, &source[line_start..line_end])
}
