# REPL-agent evaluation policy

Owner: QA. Purpose: measure whether the delivered REPL agent completes real compiler-use tasks and identify useful context improvements. Agent conformance remains governed by the REPL specification and its deterministic tests; model-quality results are diagnostic observations, not language acceptance gates.

## Corpus

- Use fixed, replayable tasks from actual assistance sessions or observed compiler-use problems. Record provenance and distinguish verbatim replay from a newly written adaptation.
- Fix the starting project/session, prompt sequence and independently checkable outcome. Preserve exact source files and hashes, including the grader. Do not grade the agent's claim of completion as task completion.
- Include only tasks whose required observable is established. A task summary without input data or expected behavior is a candidate, not a runnable eval.
- Keep the suite small and name its coverage limits. The recorded `safe-dial` session describes Position/Rotation ADTs, multi-arity rotate-position and fold-rotations, but its exact prompt/data/expected results have not been recovered; it is not currently replayable.
- The current selected corpus and executable harness allocation live in [the S122 evidence delta](s122-evidence-delta.md#runnable-eval-corpus-and-policy). Automatic tuning and a broad provider comparison are not part of that slice.

## Evidence and interpretation

- Observe actual definitions and program results through the ordinary REPL or compiled artifact. Keep deterministic harness/stub evidence separate from live-model outcomes.
- Record task result independently from attribution. Wrong output, refusal, compiler defect, provider failure and missing evidence are different observations. Attribute a compiler failure only when a current compiler-only reproduction supports it.
- Retain incomplete and failed attempts. Report denominators and known compiler-blocked cases explicitly; never retry until success and report only the last run.
- A missing activity log invalidates metrics derived from it, not a separately observed program result. Production log sinks are best-effort; the runner checks the files it relies on.
- Fixes to compiler or agent behavior use their ordinary spec-traced evidence. An aggregate eval score cannot select a language semantic change or require the compiler to satisfy an invalid task.

## Existing observations

The activity-log contract is [REPL agent observability](../../repl/spec/17b-agent-observability.md); the source carrier is `src/agent/log.rs`. Extract only fields actually present:

| Observation | Source / interpretation |
|---|---|
| Completion | Independent post-turn program-result grader |
| Submitted definitions and repairs | submit/repair events by symbol and turn; a first-submit rate requires identifiable association |
| Tool use | pull events grouped by tool; zero is valid only when the required log exists |
| Stop reason | give_up cause and error_class; missing definition alone does not establish model refusal |
| Steps | steps_at_submit and steps_at_give_up; retain turn correlation with the full trace |
| Context | primer_hash and harvest_len, plus fixture/configuration hashes |
| Questions | Recorded pull question text, when present; useful input to primer/harvest investigation |
| Duration | Harness wall-clock observation |
| Tokens/cost | Actual provider telemetry when supplied; otherwise unknown, never inferred from text length |

Raw counts and per-run observations precede derived rates. No metric is evidence that the primer covers a numerical percentage of the language.

## Comparable runs

- Record the actual executable path/hash, source revision and dirty diff, features/configuration, fixture/prompt/probe/grader hashes, provider/model/endpoint, request settings, consent/autonomy, run limits and repeat number. Never retain credential values in reports.
- Start each repeat in a fresh isolated process/project/cache. Keep the agent-feature build in its separate target directory, following `tests/scripts/run-agent-lane.sh`.
- Compare only matching task and execution strata, or explicitly identify the changed compiler/context/model dimension. Identical hashes do not eliminate model nondeterminism.
- Choose live-provider disclosure, model and budget before execution. One run is a smoke observation; a small repeated baseline is descriptive, not evidence of statistical significance.
- A proposed primer/harvest change follows observed failure analysis. Re-run the same fixed tasks after the change; retain regressions as well as improvements. Do not turn the measurement loop into automatic production prompt editing.

## Handoff

QA owns task conditions, classifications and adequacy. Test owns runner, fixtures, graders and report generation. Binary/int design/dev owns any demonstrated production agent seam gap or selected primer/harvest correction. Sprint coordinates live-run decisions and uses the reported limitations to choose later work.
