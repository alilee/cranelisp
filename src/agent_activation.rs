//! The embedded agent's activation answer and the REPL lines rendered from it
//! (`repl/spec/00-cli-invocation.md` §0.6.1; `repl/spec/17-embedded-agent.md`
//! §17.4, §17.10.3; `design/int/agent.md` §6.3).
//!
//! The type exists in every build so the startup banner has one line builder:
//! an agent-free build answers [`AgentActivation::NotBuiltIn`]. Neither line
//! names where a setting came from (`design/int/environment.md` §2.7).

use std::fmt;

/// The variable that selects the provider; activation requires it.
pub(crate) const PROVIDER_VAR: &str = "CRANELISP_AGENT_PROVIDER";

/// The session's agent state, decided once at REPL start-up.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum AgentActivation {
    /// The binary was built without the `agent` feature.
    #[cfg_attr(
        feature = "agent",
        allow(dead_code, reason = "only the agent-free build answers this")
    )]
    NotBuiltIn,
    /// `--no-agent` was given.
    Off,
    /// Enabled, but no provider can be reached; nothing is transmitted.
    Dormant(DormantReason),
    /// Enabled with a reachable provider.
    Active {
        provider: &'static str,
        /// The model id, when one is configured (only the `stub` provider runs
        /// without one).
        model: Option<String>,
    },
}

/// Why an enabled agent is dormant: what the user must set.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum DormantReason {
    /// `CRANELISP_AGENT_PROVIDER` is unset or empty.
    NoProvider,
    /// `CRANELISP_AGENT_PROVIDER` names no provider; carries the value.
    UnrecognisedProvider(String),
    /// The selected provider's configuration is incomplete.
    Incomplete {
        provider: &'static str,
        /// What to set, as the user would read it.
        missing: String,
    },
    /// The selected provider's client could not be built.
    Failed {
        provider: &'static str,
        cause: String,
    },
}

impl AgentActivation {
    /// The one startup line that follows the existing banner (§0.6.1). Exactly
    /// one of the state words `active`, `dormant`, `off` or `not built in`.
    pub(crate) fn banner_line(&self) -> String {
        match self {
            AgentActivation::NotBuiltIn => "agent: not built in".to_string(),
            AgentActivation::Off => "agent: off (--no-agent)".to_string(),
            AgentActivation::Dormant(_) => "agent: dormant (/ask shows what to set)".to_string(),
            AgentActivation::Active {
                provider,
                model: Some(model),
            } => format!("agent: active ({provider}, model {})", one_line(model)),
            AgentActivation::Active {
                provider,
                model: None,
            } => format!("agent: active ({provider})"),
        }
    }

    /// The `/ask` notice when the agent cannot take a turn; `None` when active.
    pub(crate) fn inactive_notice(&self) -> Option<String> {
        match self {
            AgentActivation::Active { .. } => None,
            AgentActivation::NotBuiltIn => Some("agent not built in".to_string()),
            AgentActivation::Off => Some("agent off for this session (--no-agent)".to_string()),
            AgentActivation::Dormant(reason) => Some(format!(
                "agent dormant: {reason}. A turn transmits your message and \
                 harvested source excerpts to the provider."
            )),
        }
    }
}

/// `text` with each control character written as its Rust escape, so a
/// configured value cannot break or restyle the line it is shown on.
fn one_line(text: &str) -> String {
    text.chars()
        .map(|c| {
            if c.is_control() {
                c.escape_default().to_string()
            } else {
                c.to_string()
            }
        })
        .collect()
}

impl fmt::Display for DormantReason {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DormantReason::NoProvider => write!(
                f,
                "no provider selected; set {PROVIDER_VAR} to anthropic, ollama or stub"
            ),
            DormantReason::UnrecognisedProvider(value) => write!(
                f,
                "{PROVIDER_VAR} is `{value}`, which is not a provider; \
                 use anthropic, ollama or stub"
            ),
            DormantReason::Incomplete { provider, missing } => {
                write!(f, "the {provider} provider needs {missing}")
            }
            DormantReason::Failed { provider, cause } => {
                write!(f, "the {provider} provider could not start: {cause}")
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn every_state() -> Vec<(AgentActivation, &'static str)> {
        vec![
            (AgentActivation::NotBuiltIn, "not built in"),
            (AgentActivation::Off, "off"),
            (
                AgentActivation::Dormant(DormantReason::NoProvider),
                "dormant",
            ),
            (
                AgentActivation::Active {
                    provider: "stub",
                    model: Some("m-1".to_string()),
                },
                "active",
            ),
        ]
    }

    // spec: repl/spec/00-cli-invocation.md §0.6.1 — one line, one state word
    #[test]
    fn each_banner_line_carries_exactly_its_own_state_word() {
        let words = ["not built in", "off", "dormant", "active"];
        for (state, word) in every_state() {
            let line = state.banner_line();
            assert!(!line.contains('\n'), "{line:?}");
            for other in words {
                let present = regex::Regex::new(&format!(r"\b{other}\b"))
                    .unwrap()
                    .is_match(&line);
                assert_eq!(present, other == word, "{line:?} and {other:?}");
            }
        }
    }

    // spec: repl/spec/00-cli-invocation.md §0.6.1 — an active banner names provider and model
    #[test]
    fn the_active_banner_names_provider_and_model() {
        let line = AgentActivation::Active {
            provider: "ollama",
            model: Some("llama-x".to_string()),
        }
        .banner_line();
        assert!(
            line.contains("ollama") && line.contains("llama-x"),
            "{line}"
        );
        let stub = AgentActivation::Active {
            provider: "stub",
            model: None,
        }
        .banner_line();
        assert_eq!(stub, "agent: active (stub)");
    }

    // spec: repl/spec/00-cli-invocation.md §0.6.1 — a configured model with line breaks or
    // other control characters still renders one identifiable line (review R2)
    #[test]
    fn a_multiline_model_renders_on_one_physical_line() {
        let line = AgentActivation::Active {
            provider: "stub",
            model: Some("review-model\nagent: off\r\x1b[2J\tend".to_string()),
        }
        .banner_line();
        assert_eq!(line.lines().count(), 1, "{line:?}");
        assert!(!line.chars().any(char::is_control), "{line:?}");
        assert_eq!(
            line,
            r"agent: active (stub, model review-model\nagent: off\r\u{1b}[2J\tend)"
        );
    }

    // spec: repl/spec/17-embedded-agent.md §17.10.3 — the dormant notice names what to set
    #[test]
    fn dormant_notices_name_what_to_set() {
        let notice = |reason| {
            AgentActivation::Dormant(reason)
                .inactive_notice()
                .expect("dormant has a notice")
        };
        assert!(notice(DormantReason::NoProvider).contains(PROVIDER_VAR));
        assert!(
            notice(DormantReason::UnrecognisedProvider("bogus".to_string())).contains("`bogus`")
        );
        let incomplete = notice(DormantReason::Incomplete {
            provider: "ollama",
            missing: "CRANELISP_AGENT_MODEL".to_string(),
        });
        assert!(incomplete.contains("ollama") && incomplete.contains("CRANELISP_AGENT_MODEL"));
        assert_eq!(
            AgentActivation::Active {
                provider: "stub",
                model: None
            }
            .inactive_notice(),
            None
        );
    }
}
