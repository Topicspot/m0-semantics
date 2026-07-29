> **Status: frozen, and not what this repository is about.**
>
> This repository is now [M₀](../README.md) — the formal semantics work that grew out of the
> language experiment. Weave, the systems language below, is kept here because its history
> lives in this repository. No work is planned on it right now; the last state is a Phase 1 +
> Phase 2 specification, a Rust lexer and a diagnostics crate, with the parser as the next
> milestone.

# Weave

**Weave** is a new systems & backend programming language in early development:
memory safety and data-race freedom proven by the compiler (ownership + region
inference, **no lifetime syntax**), BEAM-style lightweight isolated processes
with **structured concurrency only** (no `async/await`, no function coloring),
**effects-as-capabilities** in the type system, and `comptime` metaprogramming
in the language itself.

```weave
fn fetch_greeting(name: &String) -> Result<String, NetError> ! {net.Connect} {
    let response = http.get("https://api.example.com/greet/{name}")?
    Ok(response.body)
}

fn main() ! {net.Connect} {
    scope {
        let a = spawn { fetch_greeting("Ada") }
        let b = spawn { fetch_greeting("Grace") }
        println("{a.join()?} and {b.join()?}")
    }
}
```

## Status

⚠️ **Pre-alpha, design-first.** The language specification is being written and
the compiler is a bootstrap prototype (Rust). Nothing here is stable.

| Milestone | Status |
|---|---|
| Phase 1 spec — core architecture (memory, effects, concurrency, grammar core) | ✅ [`docs/spec/phase1_core_spec.md`](docs/spec/phase1_core_spec.md) |
| Lexer (Unicode-secure, error-resilient, auto statement termination) | ✅ `crates/weave_lexer` |
| Phase 2 spec — formal grammar, typing/region/effect rules, exec semantics | ✅ [`docs/spec/phase2_formal_spec.md`](docs/spec/phase2_formal_spec.md) |
| Parser → AST | 🔜 next |
| Type/region/effect checking (HIR) | planned |
| Cranelift debug backend | planned |

## Design pillars

1. **Safety is proven, not documented.** Ownership + borrow checking with fully
   inferred regions; signatures use readable `from` provenance clauses
   (`fn get(m: &Map<K,V>, k: K) -> &V from m`) instead of lifetime annotations.
2. **Capabilities, not colors.** A function's type declares what it may *do*
   (`! {fs.Read, net.Connect}`), not how it is scheduled. Concurrency is
   `scope`/`spawn` structured processes with isolated heaps — no global GC,
   no shared mutable state, no colored functions.
3. **One language all the way down.** Compile-time metaprogramming is ordinary
   Weave executed by the compiler (`comptime`) — no macro sublanguage.
4. **Tooling is the product.** Query-based incremental compiler shared by CLI
   and LSP, two backends (fast debug via Cranelift, optimized release via
   MLIR/LLVM), one `weave` binary for build/test/fmt/lint/doc/packages.
5. **Supply chain security by construction.** No code execution on package
   install, content-addressed registry, hermetic deterministic builds,
   capability audit of every dependency.

## Repository layout

```
crates/
  weave_diagnostics/   Structured diagnostics: spans, labels, suggestions, rendering
  weave_lexer/         Tokens + Unicode-secure error-resilient lexer (spec §2)
  weavec/              Compiler driver prototype (currently: `weavec lex file.wv`)
docs/spec/             Language specification (Phase 1+)
examples/              Weave source samples
```

## Building

```bash
cargo build
cargo test
cargo run -p weavec -- lex examples/hello.wv
```

## License

MIT OR Apache-2.0.
