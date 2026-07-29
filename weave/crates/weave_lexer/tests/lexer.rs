use weave_lexer::{lex, Keyword, TokenKind, WordOp};

fn kinds(src: &str) -> Vec<TokenKind> {
    lex(src).tokens.into_iter().map(|t| t.kind).collect()
}

fn no_errors(src: &str) {
    let out = lex(src);
    assert!(
        out.diagnostics.is_empty(),
        "unexpected diagnostics for {src:?}: {:#?}",
        out.diagnostics
    );
}

#[test]
fn keywords_and_idents() {
    use TokenKind::*;
    let out = lex("fn main");
    assert_eq!(
        out.tokens.iter().map(|t| t.kind).collect::<Vec<_>>(),
        vec![Keyword(self::Keyword::Fn), Ident, AutoTerm, Eof]
    );
    no_errors("fn main");
}

#[test]
fn all_34_keywords_recognized() {
    let kws = "fn let mut const type struct enum trait impl pub use as \
               if else match for while loop break continue return \
               scope spawn detach on_cancel defer comptime unsafe extern effect \
               true false self Self where from in";
    let out = lex(kws);
    let n = out
        .tokens
        .iter()
        .filter(|t| matches!(t.kind, TokenKind::Keyword(_)))
        .count();
    assert_eq!(n, 37); // 34 keywords incl. true/false/self/Self as listed = 37 words in the string
}

#[test]
fn word_operators() {
    let out = lex("a and b or not c");
    let ops: Vec<_> = out.tokens.iter().filter_map(|t| t.word_op).collect();
    assert_eq!(ops, vec![WordOp::And, WordOp::Or, WordOp::Not]);
}

#[test]
fn symbolic_logic_operators_rejected_with_recovery() {
    let out = lex("a && b");
    assert_eq!(out.diagnostics.len(), 1);
    assert_eq!(out.diagnostics[0].code, "W0012");
    // Recovered as `and`:
    assert!(out.tokens.iter().any(|t| t.word_op == Some(WordOp::And)));
}

#[test]
fn numbers() {
    use TokenKind::*;
    assert_eq!(
        kinds("42 0xFF 0o77 0b1010 1_000_000 42u8"),
        vec![Int, Int, Int, Int, Int, Int, AutoTerm, Eof]
    );
    assert_eq!(
        kinds("1.5 2e10 1.5f32 3f64"),
        vec![Float, Float, Float, Float, AutoTerm, Eof]
    );
    no_errors("42 0xFF 1.5 2e10 42u8 7i64 1usize");
}

#[test]
fn method_call_on_int_is_not_a_float() {
    use TokenKind::*;
    assert_eq!(
        kinds("1.abs()"),
        vec![Int, Dot, Ident, LParen, RParen, AutoTerm, Eof]
    );
}

#[test]
fn bad_suffix_flagged() {
    let out = lex("42q8");
    assert_eq!(out.diagnostics[0].code, "W0007");
}

#[test]
fn strings_and_interpolation() {
    let out = lex(r#""user {id} loaded""#);
    assert_eq!(out.tokens[0].kind, TokenKind::Str);
    assert!(out.tokens[0].has_interpolation);

    let out = lex(r#""plain" "esc {{x}}""#);
    assert!(!out.tokens[0].has_interpolation);
    assert!(
        !out.tokens[1].has_interpolation,
        "escaped braces are not interpolation"
    );
}

#[test]
fn raw_and_byte_strings() {
    use TokenKind::*;
    assert_eq!(
        kinds(r##"r"a\b" r#"with "quote""# b"bytes""##),
        vec![RawStr, RawStr, ByteStr, AutoTerm, Eof]
    );
    no_errors(r##"r"a\b" r#"with "quote""# b"bytes""##);
}

#[test]
fn char_literals() {
    use TokenKind::*;
    assert_eq!(
        kinds(r"'a' '\n' '\u{1F600}'"),
        vec![Char, Char, Char, AutoTerm, Eof]
    );
}

#[test]
fn unterminated_string_recovers() {
    let out = lex("\"oops");
    assert_eq!(out.diagnostics[0].code, "W0010");
    assert_eq!(out.tokens.last().unwrap().kind, TokenKind::Eof);
}

#[test]
fn comments() {
    use TokenKind::*;
    assert_eq!(
        kinds("// line\n/// doc\n//! mod\n/* block /* nested */ */"),
        vec![LineComment, DocComment, ModDocComment, BlockComment, Eof]
    );
}

#[test]
fn auto_termination_go_style() {
    use TokenKind::*;
    // Newline after `b` terminates; newline after `+` does not.
    assert_eq!(
        kinds("let x = a + b\nlet y = 2"),
        vec![
            Keyword(self::Keyword::Let),
            Ident,
            Eq,
            Ident,
            Plus,
            Ident,
            AutoTerm,
            Keyword(self::Keyword::Let),
            Ident,
            Eq,
            Int,
            AutoTerm,
            Eof
        ]
    );
    assert_eq!(
        kinds("let x = a +\nb"),
        vec![
            Keyword(self::Keyword::Let),
            Ident,
            Eq,
            Ident,
            Plus,
            Ident,
            AutoTerm,
            Eof
        ]
    );
}

#[test]
fn no_auto_term_after_open_brace() {
    use TokenKind::*;
    assert_eq!(
        kinds("fn f() {\n}"),
        vec![
            Keyword(self::Keyword::Fn),
            Ident,
            LParen,
            RParen,
            LBrace,
            RBrace,
            AutoTerm,
            Eof
        ]
    );
    // AutoTerm is only ever inserted at a newline; `() {` on one line stays
    // terminator-free (spec §3.1).
}

#[test]
fn reserved_words_flagged() {
    let out = lex("let async = 1");
    assert_eq!(out.diagnostics[0].code, "W0005");
    assert!(out.tokens.iter().any(|t| t.kind == TokenKind::Reserved));
}

#[test]
fn mixed_script_identifier_rejected() {
    // Latin 'a' + Cyrillic 'о' (homoglyph attack).
    let out = lex("let aо = 1");
    assert!(
        out.diagnostics.iter().any(|d| d.code == "W0004"),
        "{:#?}",
        out.diagnostics
    );
}

#[test]
fn single_script_cyrillic_identifier_allowed() {
    let out = lex("let привет = 1");
    assert!(out.diagnostics.is_empty(), "{:#?}", out.diagnostics);
}

#[test]
fn bom_rejected_with_fix() {
    let out = lex("\u{FEFF}fn main() {}");
    assert_eq!(out.diagnostics[0].code, "W0001");
    assert!(!out.diagnostics[0].suggestions.is_empty());
}

#[test]
fn effect_clause_tokens() {
    use TokenKind::*;
    assert_eq!(
        kinds("fn f() ! {fs.Read}"),
        vec![
            Keyword(self::Keyword::Fn),
            Ident,
            LParen,
            RParen,
            Bang,
            LBrace,
            Ident,
            Dot,
            Ident,
            RBrace,
            AutoTerm,
            Eof
        ]
    );
}

#[test]
fn operators_full_set() {
    use TokenKind::*;
    assert_eq!(
        kinds("= += -= *= /= %= == != < <= > >= | ^ & << >> + - * / % ? -> => # ;"),
        vec![
            Eq, PlusEq, MinusEq, StarEq, SlashEq, PercentEq, EqEq, NotEq, Lt, LtEq, Gt, GtEq, Pipe,
            Caret, Amp, Shl, Shr, Plus, Minus, Star, Slash, Percent, Question, Arrow, FatArrow,
            Hash, Semi, Eof
        ]
    );
}

#[test]
fn error_resilience_garbage_input() {
    let out = lex("fn @@@ ¤¤ main");
    // Lexer never stops: stream ends with Eof and errors are collected.
    assert_eq!(out.tokens.last().unwrap().kind, TokenKind::Eof);
    assert!(out.diagnostics.iter().all(|d| d.code == "W0013"));
    assert!(!out.diagnostics.is_empty());
}
