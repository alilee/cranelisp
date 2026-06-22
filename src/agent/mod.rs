// Embedded agent — int-side module seam (Sprint 88 Phase 5, Wave 2 foundations).
//
// `design/int/agent.md` §3.1. This module is entirely `#[cfg(feature = "agent")]`
// (declared so in `lib.rs`), a sibling to `repl.rs` / `eval.rs` / `process_form.rs`
// in int's session decomposition (`src/CLAUDE.md §"Session/REPL module
// decomposition"`). Feature-off ⇒ this module does not exist and the binary is
// byte-identical to today (`agent.md §1`, `repl/spec.md §17.1`).
//
// WAVE SCOPE. This wave delivers the *seam*, not the agent: the §5.3 dispatch
// classifier entry point (`classify_for_agent`) and a minimal `agent_turn`
// placeholder with the stable signature. The real loop (rig `CompletionModel`,
// harvester, primer, pull-as-visible-commands) lands in Wave 3 — `agent.md §6`
// is explicit that the `rig-core` dep is NOT added until then. Keeping the
// signature + module seam stable now is the Wave-2 foundation.

use std::io::Write;

use crate::session_v4::CompilerSession;

/// The dispatch-classifier routing decision (`agent.md §2.2`,
/// `repl/spec.md §17.1`). Computed one step earlier than evaluation, in the
/// `main.rs` read loop, on a *complete* buffer. The classifier never calls the
/// model — it routes purely on the parse result + the feature cut.
///
/// Only the `Agent` arm diverts from today's behaviour, and it only fires on
/// input that today produces a parse-error diagnostic anyway — so the
/// feature-OFF build is byte-identical by construction (the variant does not
/// exist there because the whole module is `#[cfg]`-gated).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Classify {
    /// Route to the deterministic REPL unchanged — slash command, blank/comment,
    /// or a buffer the reader accepts (a complete sexp / atom / literal: the §4
    /// self-documentation surface). Falls through to `process_commands`.
    Repl,
    /// Unclosed `(` / `[` — the existing `parens_balanced` continuation gate.
    Continuation,
    /// A parse error that is NOT an unclosed bracket (natural-language prose).
    /// Routes to the agent as a turn. Carries the original text.
    Agent(String),
}

impl CompilerSession {
    /// Classify a *complete* REPL buffer for agent dispatch (`agent.md §2.2`,
    /// `repl/spec.md §17.1` — refined classifier, user-directed 2026-06-22).
    ///
    /// Parseability alone is insufficient: this reader accepts a run of bare
    /// words (`how do I define a function`) as `Ok(N Symbol forms)`, so prose
    /// would otherwise route to the REPL. The refined rule resolves the bare
    /// symbols before deciding — only a buffer whose every bare atom is *known*
    /// (resolves, or is a literal) is the §4 self-documentation surface; any
    /// unbound bare symbol (a typo, a bare word, multi-word prose) is for the
    /// agent. Routing rules (first match wins):
    ///
    /// - starts with `/` → `Repl` (slash command, incl. `/ask`/`/refs`/`/tests-for`)
    /// - blank / comment-only → `Repl` (silent re-prompt)
    /// - `parse(buffer)`:
    ///   - `Err(unclosed '(' / '[')` → `Continuation` (the `parens_balanced` gate)
    ///   - `Err(other parse error)` → `Agent(text)` (not Cranelisp → prose)
    ///   - `Ok(forms)`:
    ///     - ANY compound form (`List`/`Bracket`, e.g. `(+ 1 2)`, `[1 2 3]`)
    ///       → `Repl` (it is code)
    ///     - else (all forms are bare atoms — symbols / literals):
    ///       - ALL known (every `Symbol` resolves via the same resolution path
    ///         `/info`/bare-symbol introspection uses, plus intrinsic type names;
    ///         literals always count) → `Repl` (the §4 describe surface)
    ///       - ANY unbound / unknown symbol → `Agent(text)`
    ///
    /// The symbol-lookup → `Agent` divergence lives ENTIRELY in this module,
    /// which is `#[cfg(feature = "agent")]`-gated (`lib.rs`): feature-off this
    /// method does not exist and the binary is byte-identical to today — a bare
    /// unbound symbol reaches today's `eval.rs` "unbound" introspection message
    /// via `process_commands`, not the agent.
    pub fn classify_for_agent(&self, buffer: &str) -> Classify {
        use cranelisp_types::Sexp;

        let trimmed = buffer.trim();

        // Slash command — unchanged path. (`/ask <text>` is dispatched to the
        // agent by `process_commands` → `dispatch_command`, not here.)
        if trimmed.starts_with('/') {
            return Classify::Repl;
        }

        // Blank / comment-only — unchanged (process_commands::Nothing).
        if trimmed.is_empty() || crate::session_v4::is_comment_only(trimmed) {
            return Classify::Repl;
        }

        // Consult the same reader the REPL already trusts.
        let forms = match cranelisp_frontend::parse(buffer) {
            Ok(forms) => forms,
            Err(_) => {
                // Distinguish "unclosed bracket" (a continuation the reader is
                // still waiting on) from a genuine parse error (prose). The REPL
                // read loop already gates continuations via `parens_balanced`
                // BEFORE reaching the classifier, so by the time we are here the
                // buffer is "complete" by the paren-balance test. A residual
                // parse error on a paren-balanced buffer is therefore NOT an
                // unclosed bracket — it is prose. But guard defensively: if the
                // buffer is somehow unbalanced, treat it as a continuation
                // rather than diverting to the agent.
                return if !crate::session_v4::parens_balanced(buffer) {
                    Classify::Continuation
                } else {
                    Classify::Agent(trimmed.to_string())
                };
            }
        };

        // `Ok(forms)`. Any compound form (a list/vector/application) is code —
        // route to the deterministic REPL untouched.
        let any_compound = forms
            .iter()
            .any(|f| matches!(f, Sexp::List(..) | Sexp::Bracket(..)));
        if any_compound {
            return Classify::Repl;
        }

        // Every form is a bare atom. Literals always count as known; a bare
        // `Symbol` is known iff it resolves through the same path bare-symbol
        // introspection / `/info` use (`lookup_with_prelude_fallback`: current
        // module → prelude outer scope → root, covering bound defs, special
        // forms, types, traits, operators, constructors), or it names an
        // intrinsic type (`Int`/`Bool`/`Float`/`String`, the §4.1.3 surface that
        // resolves outside the tables). ANY unbound symbol → the agent.
        let all_known = forms.iter().all(|f| match f {
            Sexp::Symbol(name, _) => self.symbol_is_known(name),
            Sexp::Int(..) | Sexp::Float(..) | Sexp::Bool(..) | Sexp::Str(..) => true,
            // No compound forms remain (handled above); a residual Comment is
            // inert (the comment-only buffer already routed to Repl) — treat as
            // known so it does not divert to the agent.
            _ => true,
        });

        if all_known {
            Classify::Repl
        } else {
            Classify::Agent(trimmed.to_string())
        }
    }

    /// Is a bare symbol *known* to the session — i.e. would the §4 bare-symbol
    /// introspection / `/info` path describe it rather than report it unbound?
    ///
    /// Reuses the canonical resolution path (`lookup_with_prelude_fallback`,
    /// the same `Some`/`None` gate `/sig`/`/info`/`describe_symbol` use to
    /// distinguish a described symbol from `unknown symbol '…'`), plus the
    /// intrinsic-type-name check those paths apply ahead of the table lookup
    /// (`Int`/`Bool`/`Float`/`String` — §4.1.3 names that live outside the
    /// symbol tables). No second resolver is hand-rolled (Principle 7).
    fn symbol_is_known(&self, name: &str) -> bool {
        crate::session_v4::intrinsic_type_from_name(name).is_some()
            || self.lookup_with_prelude_fallback(name).is_some()
    }

    /// Take one agent turn over the user's text (`agent.md §3.2`).
    ///
    /// WAVE-2 PLACEHOLDER. The real model↔tool loop (rig `CompletionModel`,
    /// request assembly, harvest, pull-as-visible-commands, prose framing) is
    /// Wave 3. This placeholder holds the stable signature (`&mut CompilerSession`
    /// plus the user text plus the output sink) so the `agent` feature COMPILES
    /// and the dispatch wiring (the `main.rs` read-loop arm and the `/ask` arm)
    /// is real. It renders a single framed notice that the agent is unimplemented.
    pub fn agent_turn(&mut self, text: &str, stdout: &mut impl Write) {
        let _ = text;
        let body = "agent not yet implemented (Wave 3)";
        let _ = write!(stdout, "{}", crate::style::agent_prose(body));
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::session_v4::{SessionSettings, RunMode};
    use cranelisp_types::CodegenBehaviour;

    /// Build a minimal REPL-mode session for classifier unit tests. The agent
    /// classifier is a pure routing decision over `parse` + the feature cut, so
    /// it needs only a constructed session, no compiled state.
    fn repl_session() -> CompilerSession {
        let tmp = tempfile::tempdir().unwrap();
        let settings = SessionSettings {
            no_color: true,
            no_cache: true,
            codegen_behaviour: CodegenBehaviour::InMemoryAndObject,
            priority_workers: 1,
            nice_workers: 1,
            run_mode: RunMode::Repl,
        };
        // Keep the tempdir alive for the session's lifetime by leaking it — these
        // are short-lived unit-test sessions and the dir is OS-tmp.
        let root = tmp.keep();
        CompilerSession::new(settings, root, "user")
    }

    // spec: repl/spec.md §17.1 — a complete form routes to the deterministic REPL.
    #[test]
    fn form_routes_to_repl() {
        let s = repl_session();
        assert_eq!(s.classify_for_agent("(add-i64 1 2)"), Classify::Repl);
    }

    // spec: repl/spec.md §17.1 — a slash command routes to the deterministic REPL.
    #[test]
    fn slash_routes_to_repl() {
        let s = repl_session();
        assert_eq!(s.classify_for_agent("/list"), Classify::Repl);
    }

    // spec: repl/spec.md §17.1 — blank / comment-only routes to the REPL.
    #[test]
    fn blank_and_comment_route_to_repl() {
        let s = repl_session();
        assert_eq!(s.classify_for_agent(""), Classify::Repl);
        assert_eq!(s.classify_for_agent("   "), Classify::Repl);
        assert_eq!(s.classify_for_agent("; just a comment"), Classify::Repl);
    }

    // spec: repl/spec.md §17.1 — a bare KNOWN symbol STILL routes to the REPL
    // (the §4 self-documentation surface is preserved; the agent does NOT
    // intercept a symbol that resolves). `if`/`defn` are special forms seeded at
    // root in every session; an intrinsic type name (`Int`) resolves outside the
    // tables. Both are "known" by the same resolution path `/info`/§4 use.
    #[test]
    fn bare_known_symbol_routes_to_repl() {
        let s = repl_session();
        assert_eq!(s.classify_for_agent("if"), Classify::Repl);
        assert_eq!(s.classify_for_agent("defn"), Classify::Repl);
        assert_eq!(s.classify_for_agent("Int"), Classify::Repl);
    }

    // spec: repl/spec.md §17.1 — a literal always counts as known and routes to
    // the REPL (the §4 bare-value display).
    #[test]
    fn bare_literal_routes_to_repl() {
        let s = repl_session();
        assert_eq!(s.classify_for_agent("42"), Classify::Repl);
        assert_eq!(s.classify_for_agent("3.14"), Classify::Repl);
        assert_eq!(s.classify_for_agent("true"), Classify::Repl);
        assert_eq!(s.classify_for_agent("\"hi\""), Classify::Repl);
    }

    // spec: repl/spec.md §17.1 — a bare UNKNOWN symbol (a bare word, or a typo)
    // routes to the agent: it does NOT resolve through the introspection path,
    // so the refined classifier hands it to the agent rather than the §4
    // "unbound" message. (Feature-off this divergence does not exist — see the
    // Lane-B guard in tests/agent.rs.)
    #[test]
    fn bare_unknown_symbol_routes_to_agent() {
        let s = repl_session();
        match s.classify_for_agent("yes") {
            Classify::Agent(text) => assert_eq!(text, "yes"),
            other => panic!("expected Agent for bare unknown 'yes', got {other:?}"),
        }
        match s.classify_for_agent("lenght") {
            Classify::Agent(text) => assert_eq!(text, "lenght"),
            other => panic!("expected Agent for typo 'lenght', got {other:?}"),
        }
    }

    // spec: repl/spec.md §17.1 — a compound form (list / vector) is code and
    // routes to the REPL, regardless of whether its head resolves.
    #[test]
    fn compound_form_routes_to_repl() {
        let s = repl_session();
        // `add-i64` is not bound in this bare session, but a list is code.
        assert_eq!(s.classify_for_agent("(add-i64 1 2)"), Classify::Repl);
        assert_eq!(s.classify_for_agent("[1 2 3]"), Classify::Repl);
    }

    // spec: repl/spec.md §17.1 — multi-word prose parses as a run of bare
    // symbols (`Ok`), but those symbols do not resolve, so the refined
    // classifier routes it to the agent (the any-unbound rule). This is the U1
    // gap the refinement closes: parseability is insufficient.
    #[test]
    fn unsigiled_multiword_prose_routes_to_agent() {
        let s = repl_session();
        match s.classify_for_agent("how do I define a function") {
            Classify::Agent(text) => assert_eq!(text, "how do I define a function"),
            other => panic!("expected Agent for prose, got {other:?}"),
        }
    }

    // spec: repl/spec.md §17.1 — a buffer mixing a known bare symbol with an
    // unknown one routes to the agent (any-unbound wins). `if` is known; `frob`
    // is not.
    #[test]
    fn mixed_known_and_unknown_routes_to_agent() {
        let s = repl_session();
        match s.classify_for_agent("if frob") {
            Classify::Agent(text) => assert_eq!(text, "if frob"),
            other => panic!("expected Agent for mixed known+unknown, got {other:?}"),
        }
    }

    // spec: repl/spec.md §17.1 — a non-bracket parse error (stray `)`,
    // unterminated string) routes to the agent.
    #[test]
    fn non_bracket_parse_error_routes_to_agent() {
        let s = repl_session();
        match s.classify_for_agent(")") {
            Classify::Agent(text) => assert_eq!(text, ")"),
            other => panic!("expected Agent for stray ')', got {other:?}"),
        }
        match s.classify_for_agent("\"unterminated") {
            Classify::Agent(_) => {}
            other => panic!("expected Agent for unterminated string, got {other:?}"),
        }
    }

    // spec: repl/spec.md §17.1 — an unclosed paren routes to continuation, NOT
    // the agent (the parens-balanced gate).
    #[test]
    fn unclosed_paren_routes_to_continuation() {
        let s = repl_session();
        assert_eq!(s.classify_for_agent("(add-i64 1"), Classify::Continuation);
    }
}
