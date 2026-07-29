//! Diagnostics infrastructure for the Weave compiler.
//!
//! Design contract (Phase 1 spec §9.2): diagnostics are structured data with a
//! stable machine-readable shape; the human renderer is just one consumer.
//! Every diagnostic carries at least one labeled span and, where possible, a
//! concrete suggestion. Error codes are stable (`W####`) and documented.

/// A byte-offset span into a single source file. Lossless and cheap to copy.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Span {
    pub start: u32,
    pub end: u32,
}

impl Span {
    pub fn new(start: u32, end: u32) -> Self {
        debug_assert!(start <= end, "span start must not exceed end");
        Span { start, end }
    }

    pub fn len(&self) -> u32 {
        self.end - self.start
    }

    pub fn is_empty(&self) -> bool {
        self.start == self.end
    }

    /// Smallest span covering both.
    pub fn to(&self, other: Span) -> Span {
        Span::new(self.start.min(other.start), self.end.max(other.end))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Severity {
    Error,
    Warning,
    Note,
}

/// A labeled span inside a diagnostic ("this reference is created here").
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Label {
    pub span: Span,
    pub message: String,
}

/// A machine-applicable fix suggestion.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Suggestion {
    pub span: Span,
    pub replacement: String,
    pub message: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Diagnostic {
    /// Stable error code, e.g. "W0001". Never reused for a different meaning.
    pub code: &'static str,
    pub severity: Severity,
    pub message: String,
    pub primary: Label,
    pub secondary: Vec<Label>,
    pub suggestions: Vec<Suggestion>,
}

impl Diagnostic {
    pub fn error(
        code: &'static str,
        message: impl Into<String>,
        span: Span,
        label: impl Into<String>,
    ) -> Self {
        Diagnostic {
            code,
            severity: Severity::Error,
            message: message.into(),
            primary: Label {
                span,
                message: label.into(),
            },
            secondary: Vec::new(),
            suggestions: Vec::new(),
        }
    }

    pub fn with_secondary(mut self, span: Span, message: impl Into<String>) -> Self {
        self.secondary.push(Label {
            span,
            message: message.into(),
        });
        self
    }

    pub fn with_suggestion(
        mut self,
        span: Span,
        replacement: impl Into<String>,
        message: impl Into<String>,
    ) -> Self {
        self.suggestions.push(Suggestion {
            span,
            replacement: replacement.into(),
            message: message.into(),
        });
        self
    }
}

/// Maps byte offsets to 1-based (line, column) pairs for human rendering.
pub struct LineIndex {
    /// Byte offset of the start of each line.
    line_starts: Vec<u32>,
}

impl LineIndex {
    pub fn new(text: &str) -> Self {
        let mut line_starts = vec![0u32];
        for (i, b) in text.bytes().enumerate() {
            if b == b'\n' {
                line_starts.push(i as u32 + 1);
            }
        }
        LineIndex { line_starts }
    }

    /// Returns (line, column), both 1-based. Column counts bytes within the line.
    pub fn line_col(&self, offset: u32) -> (u32, u32) {
        let line = match self.line_starts.binary_search(&offset) {
            Ok(l) => l,
            Err(l) => l - 1,
        };
        (line as u32 + 1, offset - self.line_starts[line] + 1)
    }
}

/// Renders a diagnostic to a human-readable string (single-file variant).
pub fn render(diag: &Diagnostic, file_name: &str, source: &str) -> String {
    let index = LineIndex::new(source);
    let (line, col) = index.line_col(diag.primary.span.start);
    let sev = match diag.severity {
        Severity::Error => "error",
        Severity::Warning => "warning",
        Severity::Note => "note",
    };
    let mut out = format!(
        "{sev}[{}]: {}\n  --> {file_name}:{line}:{col}\n",
        diag.code, diag.message
    );
    if !diag.primary.message.is_empty() {
        out.push_str(&format!("   = {}\n", diag.primary.message));
    }
    for label in &diag.secondary {
        let (l, c) = index.line_col(label.span.start);
        out.push_str(&format!("   - {file_name}:{l}:{c}: {}\n", label.message));
    }
    for s in &diag.suggestions {
        out.push_str(&format!("   help: {} -> `{}`\n", s.message, s.replacement));
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn line_index_maps_offsets() {
        let idx = LineIndex::new("ab\ncd\n");
        assert_eq!(idx.line_col(0), (1, 1));
        assert_eq!(idx.line_col(1), (1, 2));
        assert_eq!(idx.line_col(3), (2, 1));
        assert_eq!(idx.line_col(5), (2, 3));
    }

    #[test]
    fn span_join() {
        assert_eq!(Span::new(2, 4).to(Span::new(7, 9)), Span::new(2, 9));
    }
}
