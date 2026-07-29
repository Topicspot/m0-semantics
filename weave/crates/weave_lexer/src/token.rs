//! Token definitions for Weave v0.1 (Phase 1 spec §2).

use weave_diagnostics::Span;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TokenKind {
    // ── Identifiers & keywords ────────────────────────────────────────────
    Ident,
    Keyword(Keyword),
    /// Reserved for future editions (§2.2); using one is an error, but the
    /// lexer still produces the token so the parser can recover.
    Reserved,

    // ── Literals ──────────────────────────────────────────────────────────
    Int,
    Float,
    /// String literal. `has_interpolation` on the token payload marks `{expr}` parts.
    Str,
    RawStr,
    ByteStr,
    Char,

    // ── Comments (kept as tokens: needed by fmt/doc/LSP, §2.3) ───────────
    LineComment,
    BlockComment,
    DocComment,    // ///
    ModDocComment, // //!

    // ── Operators & punctuation ──────────────────────────────────────────
    Eq, // =
    PlusEq,
    MinusEq,
    StarEq,
    SlashEq,
    PercentEq,
    EqEq,
    NotEq,
    Lt,
    LtEq,
    Gt,
    GtEq,
    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    Amp,    // &
    AmpMut, // `&mut` is two tokens; kept for doc clarity — not produced
    Pipe,   // |
    Caret,  // ^
    Shl,
    Shr,      // << >>
    Question, // ?
    Dot,      // .
    Comma,    // ,
    Colon,    // :
    Semi,     // ; (explicit)
    Arrow,    // ->
    FatArrow, // =>
    Bang,     // ! (effect clause)
    Hash,     // # (attributes)
    LParen,
    RParen,
    LBracket,
    RBracket,
    LBrace,
    RBrace,

    /// Automatically inserted statement terminator (§3.1, Go-style rule).
    AutoTerm,

    /// A byte sequence the lexer could not interpret. Error-resilient lexing:
    /// the parser sees this token and recovers (§9.2).
    Error,

    Eof,
}

/// The 34 v0.1 keywords (Phase 1 spec §2.2 + `defer` from Phase 2 spec §6.6).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Keyword {
    Fn,
    Let,
    Mut,
    Const,
    Type,
    Struct,
    Enum,
    Trait,
    Impl,
    Pub,
    Use,
    As,
    If,
    Else,
    Match,
    For,
    While,
    Loop,
    Break,
    Continue,
    Return,
    Scope,
    Spawn,
    Detach,
    OnCancel,
    Defer,
    Comptime,
    Unsafe,
    Extern,
    Effect,
    True,
    False,
    SelfValue,
    SelfType,
    Where,
    From,
    In,
}

pub fn keyword_from_str(s: &str) -> Option<Keyword> {
    use Keyword::*;
    Some(match s {
        "fn" => Fn,
        "let" => Let,
        "mut" => Mut,
        "const" => Const,
        "type" => Type,
        "struct" => Struct,
        "enum" => Enum,
        "trait" => Trait,
        "impl" => Impl,
        "pub" => Pub,
        "use" => Use,
        "as" => As,
        "if" => If,
        "else" => Else,
        "match" => Match,
        "for" => For,
        "while" => While,
        "loop" => Loop,
        "break" => Break,
        "continue" => Continue,
        "return" => Return,
        "scope" => Scope,
        "spawn" => Spawn,
        "detach" => Detach,
        "on_cancel" => OnCancel,
        "defer" => Defer,
        "comptime" => Comptime,
        "unsafe" => Unsafe,
        "extern" => Extern,
        "effect" => Effect,
        "true" => True,
        "false" => False,
        "self" => SelfValue,
        "Self" => SelfType,
        "where" => Where,
        "from" => From,
        "in" => In,
        _ => return None,
    })
}

/// Identifiers reserved for future editions (§2.2). `and/or/not` are word
/// operators, handled separately.
pub const RESERVED: &[&str] = &[
    "async", "await", "gpu", "yield", "macro", "dyn", "move", "ref", "box", "try",
];

/// Word operators (§2.4). Lexed as operator tokens, not identifiers.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WordOp {
    And,
    Or,
    Not,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
    /// Word operator payload when `kind == Ident`-shaped word op.
    pub word_op: Option<WordOp>,
    /// For `Str`: whether the literal contains `{expr}` interpolation parts.
    pub has_interpolation: bool,
}

impl Token {
    pub fn new(kind: TokenKind, span: Span) -> Self {
        Token {
            kind,
            span,
            word_op: None,
            has_interpolation: false,
        }
    }

    /// Whether this token may syntactically end an expression — drives
    /// automatic statement termination (§3.1).
    pub fn can_end_expression(&self) -> bool {
        use TokenKind::*;
        matches!(
            self.kind,
            Ident
                | Int
                | Float
                | Str
                | RawStr
                | ByteStr
                | Char
                | RParen
                | RBracket
                | RBrace
                | Question
                | Keyword(super::token::Keyword::True)
                | Keyword(super::token::Keyword::False)
                | Keyword(super::token::Keyword::SelfValue)
                | Keyword(super::token::Keyword::SelfType)
                | Keyword(super::token::Keyword::Break)
                | Keyword(super::token::Keyword::Continue)
                | Keyword(super::token::Keyword::Return)
        )
    }
}
