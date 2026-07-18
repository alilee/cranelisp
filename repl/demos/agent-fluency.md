# S90 Agent Fluency Demo — `/syntax` reach, sig-grain harvest, silent log

Owned by `/repl`. This documents the **agent fluency experience** delivered in
Sprint 90 (the four fluency pillars). It is **not** part of the eight-demo active
set — the active set demonstrates *the language*, played through a default
(non-agent) REPL. This demo exercises the *embedded agent's* fluency surface,
which requires an `--features agent` build, so it lives here as a recipe rather
than a `.demo` the showcase auto-plays.

Two of the four pillars are visible in a **default build** and are folded into
the active set: `/syntax` (Pillar 1) is shown live in `01-tour.demo`. The agent
flow below ties all four together.

## What this demonstrates

| Pillar | Spec | What the viewer sees |
|---|---|---|
| 1 — `/syntax` | §17.17 | The agent *reaches* for `/syntax <topic>` instead of guessing core syntax; the pull renders as a visible `agent>` command, its content is deterministic. |
| 2 — sig-grain harvest | §17.18 | The agent already knows the in-scope symbols at name + `:Type` signature + docstring — visible offline via `/context` (`== in scope ==`). |
| 4 — silent agent log | §17.20 | `CRANELISP_AGENT_LOG` captures the turn as greppable JSONL — nothing extra appears in the REPL. |

(Pillar 3, `/search`, is design-only this sprint — not demonstrated.)

## Lane D — deterministic stub-driven transcript (no provider key)

The embedded agent is driven by a **scripted stub** so the transcript is
deterministic and needs no network/provider key. The stub DSL: `tool: <name>
<arg>` synthesizes a tool-call (a visible REPL command pull); `done: <prose>` is
the terminal framed answer.

```bash
# 1. Build the agent binary (the default build does NOT contain the agent).
cargo build --features agent

# 2. Script: the agent pulls /syntax hkt, then answers.
cat > /tmp/s90_script.txt <<'EOF'
tool: syntax hkt
done: A higher-kinded type ranges a trait param over a type constructor: (deftrait (Functor f) (fmap [:(Fn [a] b) g :(f a) x] (f b))).
EOF

# 3. Drive it. CRANELISP_AGENT_LOG turns on the silent JSONL log (Pillar 4).
printf '/ask how do I write a higher-kinded type?\n/quit\n' | \
  CRANELISP_AGENT_PROVIDER=stub \
  CRANELISP_AGENT_STUB_SCRIPT=/tmp/s90_script.txt \
  CRANELISP_AGENT_LOG=/tmp/s90_agent.log \
  CRANELISP_LIB=$PWD/stdlib CRANELISP_PLATFORM_PATH=$PWD/target/debug \
  target/debug/cranelisp --agent

# 4. The log is OFF TO THE SIDE — nothing appeared in the REPL above. Mine it:
cat /tmp/s90_agent.log
grep '"event":"pull"' /tmp/s90_agent.log   # every exploration pull + its symbol
```

### Expected transcript (the three honestly-marked origins, §17.12)

```
user> /ask how do I write a higher-kinded type?
agent> /syntax hkt
TOPIC hkt  [core]
  Higher-kinded types: a trait param ranges over type constructors, applied as (f a).

  FORM
    (deftrait (Functor f) (fmap [:(Fn [a] b) g :(f a) x] (f b)))
    (impl (Functor f) (Functor Option) (defn fmap [g opt] ...))  ; slot 1 echoes head; slot 2 pairs trait + BARE ctor
    ...
  EXAMPLE
    (fmap (fn [n] (* n 2)) (Some 5))         ; (Option.Some 10)
  NOT
    (impl Functor Option ...)  -> old bare head REJECTED; echo the declared head: (impl (Functor f) (Functor Option) ...)
  ...
▌ A higher-kinded type ranges a trait param over a type constructor: (deftrait (Functor f) ...).
```

- `user>` — the human's question.
- `agent>` — the agent's *pull*, rendered as the exact REPL command it issued
  (§17.17.3 / §17.12). The content beneath it is the deterministic `/syntax`
  asset — byte-identical to what a human gets typing `/syntax hkt`.
- `▌` — the agent's framed prose answer.

### Expected log (Pillar 4, §17.20.3 — greppable JSONL)

```jsonl
{"event":"exchange","iteration":1,"ts":...}
{"event":"pull","symbol":"hkt","tool":"syntax","ts":...}
{"event":"exchange","iteration":2,"ts":...}
```

`grep '"event":"pull"'` extracts every exploration pull with its `symbol`/`tool`
— the struggle-signal the user wants to mine by hand.

## Pillar 2 — ambient sig-grain harvest (offline-auditable via `/context`)

The harvest is *ambient* — it rides every agent turn's context, with no command
and nothing extra in the REPL. Audit it offline:

```bash
printf '(defn grid-get [v i] (+ i 0))\n/context /tmp/s90_ctx.txt\n/quit\n' | \
  CRANELISP_AGENT_PROVIDER=stub CRANELISP_AGENT_STUB_SCRIPT=/dev/null \
  CRANELISP_LIB=$PWD/stdlib CRANELISP_PLATFORM_PATH=$PWD/target/debug \
  target/debug/cranelisp --agent
grep -A8 '== in scope ==' /tmp/s90_ctx.txt
```

Expected — the own defn plus prelude symbols at name + FQ `:Type` + docstring:

```
== in scope ==
:(Fn [a primitives/Int] primitives/Int) user/grid-get ; defn
:(Fn [:Num a :Num a] a) num.num/+ ; defn
:fn.threading/-> ; defmacro - Thread value through forms as first argument
...
```

The acceptance (§17.18.2): a fresh agent references an in-scope symbol's *actual*
signature without first spending a turn on `/list`/`/imports`/`/exports`.

## Live smoke (with a real provider)

The strongest evidence (S88/S89 Phase-6 pattern) is a live smoke with a real
provider key. Set `CRANELISP_AGENT_PROVIDER=anthropic` + the provider key, build
`--features agent`, and `/ask` a question whose answer needs a syntax point the
model is unsure of (e.g. "write a Functor impl for a user type"). Watch for the
agent issuing `agent> /syntax <topic>` of its own accord, the framed answer
grounding on the pulled content, and the JSONL log accumulating `pull`/`exchange`
records. Recommended to the user as the S90 fluency confirmation.
