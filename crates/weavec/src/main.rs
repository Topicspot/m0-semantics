//! `weavec` — the Weave compiler driver (prototype).
//!
//! Current capability (implementation Stage 0 prototype):
//!   weavec lex <file.wv>   — tokenize and dump the token stream + diagnostics
//!
//! The driver will grow query-based architecture per Phase 1 spec §9.1.

use std::process::ExitCode;

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args.as_slice() {
        [cmd, path] if cmd == "lex" => cmd_lex(path),
        _ => {
            eprintln!("Weave compiler prototype v0.0.1");
            eprintln!("usage: weavec lex <file.wv>");
            ExitCode::from(2)
        }
    }
}

fn cmd_lex(path: &str) -> ExitCode {
    let source = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("error: cannot read `{path}`: {e}");
            return ExitCode::from(1);
        }
    };
    let out = weave_lexer::lex(&source);
    for tok in &out.tokens {
        let text = source
            .get(tok.span.start as usize..tok.span.end as usize)
            .unwrap_or("");
        println!(
            "{:>5}..{:<5} {:?} {:?}",
            tok.span.start, tok.span.end, tok.kind, text
        );
    }
    for diag in &out.diagnostics {
        eprint!("{}", weave_diagnostics::render(diag, path, &source));
    }
    if out
        .diagnostics
        .iter()
        .any(|d| matches!(d.severity, weave_diagnostics::Severity::Error))
    {
        ExitCode::from(1)
    } else {
        ExitCode::SUCCESS
    }
}
