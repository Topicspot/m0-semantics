//! The Weave lexer (Phase 1 spec §2).
//!
//! Guarantees:
//! - **Error-resilient**: any byte sequence produces a token stream (bad input
//!   becomes `TokenKind::Error` tokens plus diagnostics); the lexer never stops.
//! - **Lossless spans**: every token carries its exact byte span.
//! - **Unicode security** (§2.1): identifiers must be NFC-normalized and must
//!   not mix scripts (trojan-source / homoglyph defense).
//! - **Automatic statement termination** (§3.1): a newline yields an `AutoTerm`
//!   token when the previous token can end an expression.

mod token;

pub use token::{keyword_from_str, Keyword, Token, TokenKind, WordOp, RESERVED};

use unicode_normalization::{is_nfc, UnicodeNormalization};
use unicode_script::{Script, UnicodeScript};
use weave_diagnostics::{Diagnostic, Span};

pub struct LexOutput {
    pub tokens: Vec<Token>,
    pub diagnostics: Vec<Diagnostic>,
}

pub fn lex(source: &str) -> LexOutput {
    let mut lexer = Lexer::new(source);
    lexer.run();
    LexOutput {
        tokens: lexer.tokens,
        diagnostics: lexer.diagnostics,
    }
}

struct Lexer<'s> {
    src: &'s str,
    /// Current byte offset.
    pos: usize,
    tokens: Vec<Token>,
    diagnostics: Vec<Diagnostic>,
    /// Kind of the last *significant* token (not comments), for AutoTerm.
    last_significant: Option<Token>,
}

impl<'s> Lexer<'s> {
    fn new(src: &'s str) -> Self {
        Lexer {
            src,
            pos: 0,
            tokens: Vec::new(),
            diagnostics: Vec::new(),
            last_significant: None,
        }
    }

    // ── Cursor helpers ────────────────────────────────────────────────────

    fn peek(&self) -> Option<char> {
        self.src[self.pos..].chars().next()
    }

    fn peek2(&self) -> Option<char> {
        let mut it = self.src[self.pos..].chars();
        it.next();
        it.next()
    }

    fn bump(&mut self) -> Option<char> {
        let c = self.peek()?;
        self.pos += c.len_utf8();
        Some(c)
    }

    fn eat(&mut self, c: char) -> bool {
        if self.peek() == Some(c) {
            self.bump();
            true
        } else {
            false
        }
    }

    fn span_from(&self, start: usize) -> Span {
        Span::new(start as u32, self.pos as u32)
    }

    fn push(&mut self, kind: TokenKind, start: usize) {
        let tok = Token::new(kind, self.span_from(start));
        self.push_token(tok);
    }

    fn push_token(&mut self, tok: Token) {
        let significant = !matches!(
            tok.kind,
            TokenKind::LineComment
                | TokenKind::BlockComment
                | TokenKind::DocComment
                | TokenKind::ModDocComment
        );
        if significant {
            self.last_significant = Some(tok.clone());
        }
        self.tokens.push(tok);
    }

    fn error(
        &mut self,
        code: &'static str,
        msg: impl Into<String>,
        span: Span,
        label: impl Into<String>,
    ) {
        self.diagnostics
            .push(Diagnostic::error(code, msg, span, label));
    }

    // ── Main loop ─────────────────────────────────────────────────────────

    fn run(&mut self) {
        if self.src.as_bytes().starts_with(&[0xEF, 0xBB, 0xBF]) {
            // BOM is forbidden (§2.1) — diagnostic with auto-fix, then skip it.
            let span = Span::new(0, 3);
            self.diagnostics.push(
                Diagnostic::error(
                    "W0001",
                    "byte order mark (BOM) is not allowed in Weave source files",
                    span,
                    "remove the BOM",
                )
                .with_suggestion(span, String::new(), "delete these bytes"),
            );
            self.pos = 3;
        }
        while self.pos < self.src.len() {
            self.next_token();
        }
        // A final AutoTerm so `a + b<EOF>` closes the last statement.
        self.maybe_auto_terminate();
        let end = self.src.len();
        self.push(TokenKind::Eof, end);
    }

    fn next_token(&mut self) {
        let start = self.pos;
        let c = match self.peek() {
            Some(c) => c,
            None => return,
        };

        match c {
            '\n' => {
                self.bump();
                self.maybe_auto_terminate();
            }
            c if c.is_whitespace() => {
                self.bump();
            }
            '/' if self.peek2() == Some('/') => self.lex_line_comment(start),
            '/' if self.peek2() == Some('*') => self.lex_block_comment(start),
            '"' => self.lex_string(start),
            'r' if matches!(self.peek2(), Some('"') | Some('#')) && self.raw_string_ahead() => {
                self.lex_raw_string(start)
            }
            'b' if self.peek2() == Some('"') => {
                self.bump(); // b
                self.lex_string_body(start, TokenKind::ByteStr);
            }
            '\'' => self.lex_char(start),
            c if c.is_ascii_digit() => self.lex_number(start),
            c if unicode_ident::is_xid_start(c) || c == '_' => self.lex_ident_or_keyword(start),
            _ => self.lex_operator(start),
        }
    }

    // ── Automatic statement termination (§3.1) ────────────────────────────

    fn maybe_auto_terminate(&mut self) {
        let should = self
            .last_significant
            .as_ref()
            .map(|t| {
                t.kind != TokenKind::AutoTerm && t.kind != TokenKind::Semi && t.can_end_expression()
            })
            .unwrap_or(false);
        if should {
            let here = self.pos.saturating_sub(1);
            self.push(TokenKind::AutoTerm, here);
        }
    }

    // ── Comments ──────────────────────────────────────────────────────────

    fn lex_line_comment(&mut self, start: usize) {
        self.bump();
        self.bump(); // //
        let kind = if self.eat('/') {
            // `////...` is a plain comment; `///` exactly is a doc comment.
            if self.peek() == Some('/') {
                TokenKind::LineComment
            } else {
                TokenKind::DocComment
            }
        } else if self.eat('!') {
            TokenKind::ModDocComment
        } else {
            TokenKind::LineComment
        };
        while let Some(c) = self.peek() {
            if c == '\n' {
                break;
            }
            self.bump();
        }
        self.push(kind, start);
    }

    fn lex_block_comment(&mut self, start: usize) {
        self.bump();
        self.bump(); // /*
        let mut depth = 1u32;
        while depth > 0 {
            match self.bump() {
                Some('/') if self.peek() == Some('*') => {
                    self.bump();
                    depth += 1;
                }
                Some('*') if self.peek() == Some('/') => {
                    self.bump();
                    depth -= 1;
                }
                Some(_) => {}
                None => {
                    let span = self.span_from(start);
                    self.error(
                        "W0002",
                        "unterminated block comment",
                        span,
                        "comment starts here",
                    );
                    break;
                }
            }
        }
        self.push(TokenKind::BlockComment, start);
    }

    // ── Identifiers, keywords, unicode security ──────────────────────────

    fn lex_ident_or_keyword(&mut self, start: usize) {
        while let Some(c) = self.peek() {
            if unicode_ident::is_xid_continue(c) || c == '_' {
                self.bump();
            } else {
                break;
            }
        }
        let text = &self.src[start..self.pos];
        let span = self.span_from(start);

        // NFC check (§2.1).
        if !is_nfc(text) {
            let normalized: String = text.nfc().collect();
            self.diagnostics.push(
                Diagnostic::error(
                    "W0003",
                    "identifier is not NFC-normalized",
                    span,
                    "non-normalized Unicode identifier",
                )
                .with_suggestion(span, normalized, "normalize the identifier"),
            );
        }

        // Mixed-script ban (§2.1): all non-Common/Inherited script codepoints
        // in one identifier must belong to a single script.
        let mut script: Option<Script> = None;
        let mut mixed = false;
        for ch in text.chars() {
            let s = ch.script();
            if s == Script::Common || s == Script::Inherited || ch == '_' {
                continue;
            }
            match script {
                None => script = Some(s),
                Some(prev) if prev != s => {
                    mixed = true;
                    break;
                }
                _ => {}
            }
        }
        if mixed {
            self.error(
                "W0004",
                "identifier mixes characters from multiple Unicode scripts",
                span,
                "mixed-script identifiers are rejected (trojan-source defense, spec §2.1)",
            );
        }

        // Word operators (§2.4).
        let word_op = match text {
            "and" => Some(WordOp::And),
            "or" => Some(WordOp::Or),
            "not" => Some(WordOp::Not),
            _ => None,
        };
        if let Some(op) = word_op {
            let mut tok = Token::new(TokenKind::Ident, span);
            tok.word_op = Some(op);
            self.push_token(tok);
            return;
        }

        if let Some(kw) = keyword_from_str(text) {
            self.push(TokenKind::Keyword(kw), start);
        } else if RESERVED.contains(&text) {
            self.error(
                "W0005",
                format!("`{text}` is reserved for a future edition of Weave"),
                span,
                "reserved word used as identifier",
            );
            self.push(TokenKind::Reserved, start);
        } else {
            self.push(TokenKind::Ident, start);
        }
    }

    // ── Numbers (§2.3) ────────────────────────────────────────────────────

    fn lex_number(&mut self, start: usize) {
        let mut is_float = false;
        if self.peek() == Some('0') && matches!(self.peek2(), Some('x') | Some('o') | Some('b')) {
            self.bump();
            let radix_char = self.bump().unwrap();
            let radix_ok = |c: char| match radix_char {
                'x' => c.is_ascii_hexdigit(),
                'o' => ('0'..='7').contains(&c),
                'b' => c == '0' || c == '1',
                _ => unreachable!(),
            };
            let mut any = false;
            while let Some(c) = self.peek() {
                if radix_ok(c) || c == '_' {
                    any |= c != '_';
                    self.bump();
                } else {
                    break;
                }
            }
            if !any {
                let span = self.span_from(start);
                self.error(
                    "W0006",
                    "numeric literal has a radix prefix but no digits",
                    span,
                    "expected digits after prefix",
                );
            }
        } else {
            self.eat_decimal_digits();
            // Fraction: only if `.` is followed by a digit (so `1.method()` works).
            if self.peek() == Some('.') && self.peek2().map_or(false, |c| c.is_ascii_digit()) {
                is_float = true;
                self.bump();
                self.eat_decimal_digits();
            }
            // Exponent.
            if matches!(self.peek(), Some('e') | Some('E')) {
                let save = self.pos;
                self.bump();
                if matches!(self.peek(), Some('+') | Some('-')) {
                    self.bump();
                }
                if self.peek().map_or(false, |c| c.is_ascii_digit()) {
                    is_float = true;
                    self.eat_decimal_digits();
                } else {
                    self.pos = save; // `1e` was actually `1` then ident `e...`
                }
            }
        }
        // Type suffix: i8..i64, u8..u64, usize, isize, f32, f64.
        let suffix_start = self.pos;
        while let Some(c) = self.peek() {
            if c.is_ascii_alphanumeric() {
                self.bump();
            } else {
                break;
            }
        }
        let suffix = &self.src[suffix_start..self.pos];
        const SUFFIXES: &[&str] = &[
            "i8", "i16", "i32", "i64", "u8", "u16", "u32", "u64", "usize", "isize", "f32", "f64",
        ];
        if !suffix.is_empty() && !SUFFIXES.contains(&suffix) {
            let span = Span::new(suffix_start as u32, self.pos as u32);
            self.error(
                "W0007",
                format!("unknown numeric type suffix `{suffix}`"),
                span,
                "expected one of i8..i64, u8..u64, usize, isize, f32, f64",
            );
        }
        if suffix.starts_with('f') && SUFFIXES.contains(&suffix) {
            is_float = true;
        }
        self.push(
            if is_float {
                TokenKind::Float
            } else {
                TokenKind::Int
            },
            start,
        );
    }

    fn eat_decimal_digits(&mut self) {
        while let Some(c) = self.peek() {
            if c.is_ascii_digit() || c == '_' {
                self.bump();
            } else {
                break;
            }
        }
    }

    // ── Strings (§2.3) ────────────────────────────────────────────────────

    fn lex_string(&mut self, start: usize) {
        self.lex_string_body(start, TokenKind::Str);
    }

    fn lex_string_body(&mut self, start: usize, kind: TokenKind) {
        self.bump(); // opening quote
        let mut has_interpolation = false;
        let mut brace_depth = 0u32;
        loop {
            match self.bump() {
                Some('"') if brace_depth == 0 => break,
                Some('\\') => match self.bump() {
                    Some('n') | Some('t') | Some('r') | Some('\\') | Some('"') | Some('0')
                    | Some('{') | Some('}') => {}
                    Some('u') => {
                        if self.eat('{') {
                            let hex_start = self.pos;
                            while self.peek().map_or(false, |c| c.is_ascii_hexdigit()) {
                                self.bump();
                            }
                            let ok = self.pos > hex_start && self.eat('}');
                            if !ok {
                                let span = self.span_from(hex_start);
                                self.error(
                                    "W0008",
                                    "malformed unicode escape",
                                    span,
                                    r"expected \u{HEX}",
                                );
                            }
                        } else {
                            let span = self.span_from(self.pos.saturating_sub(1));
                            self.error(
                                "W0008",
                                "malformed unicode escape",
                                span,
                                r"expected \u{HEX}",
                            );
                        }
                    }
                    other => {
                        let span = self.span_from(self.pos.saturating_sub(1));
                        self.error(
                            "W0009",
                            format!(
                                "unknown escape sequence `\\{}`",
                                other.map(String::from).unwrap_or_default()
                            ),
                            span,
                            "unknown escape",
                        );
                    }
                },
                Some('{') => {
                    if self.eat('{') {
                        // `{{` is a literal brace.
                    } else {
                        has_interpolation = true;
                        brace_depth += 1;
                    }
                }
                Some('}') if brace_depth > 0 => brace_depth -= 1,
                Some(_) => {}
                None => {
                    let span = self.span_from(start);
                    self.error(
                        "W0010",
                        "unterminated string literal",
                        span,
                        "string starts here",
                    );
                    break;
                }
            }
        }
        let mut tok = Token::new(kind, self.span_from(start));
        tok.has_interpolation = has_interpolation && kind == TokenKind::Str;
        self.push_token(tok);
    }

    fn raw_string_ahead(&self) -> bool {
        // At `r`, check for r"..." or r#...#"...".
        let rest = &self.src[self.pos + 1..];
        let hashes = rest.chars().take_while(|&c| c == '#').count();
        rest[hashes..].starts_with('"')
    }

    fn lex_raw_string(&mut self, start: usize) {
        self.bump(); // r
        let mut hashes = 0usize;
        while self.eat('#') {
            hashes += 1;
        }
        self.bump(); // opening quote
        'outer: loop {
            match self.bump() {
                Some('"') => {
                    let mut seen = 0usize;
                    while seen < hashes {
                        if self.peek() == Some('#') {
                            self.bump();
                            seen += 1;
                        } else {
                            continue 'outer;
                        }
                    }
                    break;
                }
                Some(_) => {}
                None => {
                    let span = self.span_from(start);
                    self.error(
                        "W0010",
                        "unterminated raw string literal",
                        span,
                        "raw string starts here",
                    );
                    break;
                }
            }
        }
        self.push(TokenKind::RawStr, start);
    }

    fn lex_char(&mut self, start: usize) {
        self.bump(); // '
        match self.bump() {
            Some('\\') => {
                self.bump();
                // Allow \u{...}
                if self.src[..self.pos].ends_with('u') && self.eat('{') {
                    while self.peek().map_or(false, |c| c.is_ascii_hexdigit()) {
                        self.bump();
                    }
                    self.eat('}');
                }
            }
            Some('\'') => {
                let span = self.span_from(start);
                self.error(
                    "W0011",
                    "empty character literal",
                    span,
                    "expected one character",
                );
                self.push(TokenKind::Error, start);
                return;
            }
            Some(_) => {}
            None => {}
        }
        if !self.eat('\'') {
            let span = self.span_from(start);
            self.error(
                "W0011",
                "unterminated character literal",
                span,
                "expected closing `'`",
            );
        }
        self.push(TokenKind::Char, start);
    }

    // ── Operators & punctuation (§2.4) ───────────────────────────────────

    fn lex_operator(&mut self, start: usize) {
        use TokenKind::*;
        let c = self.bump().unwrap();
        let kind = match c {
            '=' => {
                if self.eat('=') {
                    EqEq
                } else if self.eat('>') {
                    FatArrow
                } else {
                    Eq
                }
            }
            '+' => {
                if self.eat('=') {
                    PlusEq
                } else {
                    Plus
                }
            }
            '-' => {
                if self.eat('=') {
                    MinusEq
                } else if self.eat('>') {
                    Arrow
                } else {
                    Minus
                }
            }
            '*' => {
                if self.eat('=') {
                    StarEq
                } else {
                    Star
                }
            }
            '/' => {
                if self.eat('=') {
                    SlashEq
                } else {
                    Slash
                }
            }
            '%' => {
                if self.eat('=') {
                    PercentEq
                } else {
                    Percent
                }
            }
            '<' => {
                if self.eat('=') {
                    LtEq
                } else if self.eat('<') {
                    Shl
                } else {
                    Lt
                }
            }
            '>' => {
                if self.eat('=') {
                    GtEq
                } else if self.eat('>') {
                    Shr
                } else {
                    Gt
                }
            }
            '!' => {
                if self.eat('=') {
                    NotEq
                } else {
                    Bang
                }
            }
            '&' => {
                if self.eat('&') {
                    let span = self.span_from(start);
                    self.error(
                        "W0012",
                        "`&&` is not an operator in Weave",
                        span,
                        "logical AND is spelled `and` (spec §2.4)",
                    );
                    // Recover as `and`.
                    let mut tok = Token::new(Ident, span);
                    tok.word_op = Some(WordOp::And);
                    self.push_token(tok);
                    return;
                }
                Amp
            }
            '|' => {
                if self.eat('|') {
                    let span = self.span_from(start);
                    self.error(
                        "W0012",
                        "`||` is not an operator in Weave",
                        span,
                        "logical OR is spelled `or` (spec §2.4)",
                    );
                    let mut tok = Token::new(Ident, span);
                    tok.word_op = Some(WordOp::Or);
                    self.push_token(tok);
                    return;
                }
                Pipe
            }
            '^' => Caret,
            '?' => Question,
            '.' => Dot,
            ',' => Comma,
            ':' => Colon,
            ';' => Semi,
            '#' => Hash,
            '(' => LParen,
            ')' => RParen,
            '[' => LBracket,
            ']' => RBracket,
            '{' => LBrace,
            '}' => RBrace,
            other => {
                let span = self.span_from(start);
                self.error(
                    "W0013",
                    format!("unexpected character `{other}`"),
                    span,
                    "not valid in Weave source",
                );
                Error
            }
        };
        self.push(kind, start);
    }
}
