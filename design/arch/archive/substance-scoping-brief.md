# Brief — Substance scoping pass for architecture reconciliation

**Status.** Brief only. Spec for the substance scoping work; not the work itself. Author: `/arch` (Sprint 63 close, in-session). Addressee: the next `/arch` invocation that executes the scoping pass.

**Pairs with.** `design/arch/reconciliation-plan.md` (procedural reconciliation). The scoping pass output determines whether that plan needs a substance wave inserted before Wave 1, or stands as-is.

---

## 1. Goal

Produce a substantive per-misalignment analysis — *not* a flat classification — that determines whether the as-designed architecture (overview, principles, decisions, bounded contexts, facades, interfaces) needs material change before procedural reconciliation lands.

Each misalignment surfaced by Sprint 63's master design pass gets options + recommendation, sized so the user can act on the recommendation directly: file a Decision draft, redraft a facade, shift a bounded context, evolve a principle, or close as procedural-only.

The scoping pass is not a Decision; it is the input to a wave of Decisions, facade revisions, and BC shifts that follow.

## 2. Why this exists

The procedural reconciliation plan (`reconciliation-plan.md`) addresses where things live and how they're labelled. It does not ask whether the architecture itself is viable post-Sprint-63. The master design pass surfaced ~40 inline FIXMEs, four audit-pivot tensions, and at least four pre-identified load-bearing items (runtime BC drift, `compile_to_module` return-shape facade silence, `PlatformError` ↔ `ErrorLocation` adoption, frontend `SymbolTables` alias tension). Each could resolve as procedural cleanup or as architectural change. The scoping pass tells us which.

Acting on this matters because the procedural reorganisation should reflect the architecture's actual shape — not enshrine the pre-Sprint-63 shape and force a second rewrite when substance lands.

## 3. Inputs

Read in this order. The scoping pass needs full cross-doc synthesis; do not delegate to a subagent (isolation defeats the synthesis).

1. The six master design docs at `design/{crate}/{crate}.md` — read end-to-end. The "Open questions / proposed FIXMEs" sections are the obvious source; the substantive prose is the less obvious one (passages where the master had to caveat or work around an existing artefact).
2. The seven facade specs at `design/arch/facades/{crate}.md` (six surfaces + `types.md`).
3. `design/arch/CLAUDE.md` Decisions 1–39, `principles.md`, `bounded-contexts.md`, `overview.md`.
4. `sprints/fixmes/0001..0009-*.md` — already-filed; some master-doc inlines refine these.
5. `audits/{crate}-20260423.md` (four; runtime + platform absent — that absence is itself a misalignment).
6. `design/arch/sequences/concurrency-symbol-table-entry.{mmd,svg}` and `exec-flow-compilation.{mmd,svg}` — Sprint 63 rewrites; the rest of the sequences directory if a misalignment touches concurrency invariants.

## 4. Output

A single document at `design/arch/substance-scoping.md`. Length: honest, not padded — expected 800–1500 lines for ~15–25 substantive items (after collapse from ~40 FIXMEs). Cap is a guard against scope creep, not a target.

Each item carries the following fields, in this order:

| Field | Purpose |
|---|---|
| **Title** | Short name. Stable enough to cite from a Decision draft or sprint scope item. |
| **Description** | 2–4 sentences that orient a cold reader. State the finding (what is misaligned), name the architectural surface affected (BC / facade / Decision / principle / interface / audit), and preview the direction of the recommendation. The reader uses this to decide whether to read deep on this item. The Description is the context-shift aid — it must stand alone without the rest of the item, so a reviewer scanning twenty items can route attention without re-loading prior context. |
| **Symptom** | What the master design pass surfaced. Cite master doc § + line, plus inline FIXME or audit finding. Concrete; quote or paraphrase the surfacing prose. |
| **Tension** | Which canonical artefact is in conflict (overview / BC / facade / Decision / principle / interface / audit), and what the conflict is. State the conflict explicitly: "facade says X; master design says Y; reconciling requires Z." |
| **Stake** | What's at risk if left. Magnitude: small (editorial), medium (cross-skill rework), load-bearing (changes binding architectural commitments). Name the failure mode the misalignment leaves open. |
| **Options** | 2–3 options. Each with: shape of change; where it lands (crates + docs); effort estimate; blast radius; what's irreversible; principle citations. If an option violates a principle, evolving the principle IS one of the options — say so. If novel (no precedent in past Decisions), label "novel — no precedent" and treat as a risk multiplier. |
| **Recommendation** | One option, with rationale citing principles by number. The recommendation must be specific enough to action: "file Decision N draft with the following body shape" or "redraft `facades/X.md` §Y with the signature `…`" — not "decide this." |
| **Consequences** | What binds if accepted: Decision update (which?), facade redraft (which §?), BC shift (which surface?), principle evolution (number?), FIXME closure (which numbers?), audit re-pass trigger. |
| **Owner** | Which skill actions the recommendation. Most are `/arch` (cross-crate); some are `/design` per crate (per-crate design intent shift); some are `/sprint` (scope arbitration). |
| **Sequencing** | Gates / unlocks relative to other items in this document. Items frequently form chains (a facade silence is downstream of a Decision elevation; a BC shift unblocks two facade redrafts). State the chain. |

## 5. Discipline

**Item collapse rule.** Collapse two FIXMEs only when they cite the same underlying misalignment seen from different doc angles (e.g., the runtime BC drift surfaces in master + facade + `bounded-contexts.md` — one item, three citations). Do NOT collapse unrelated facade silences just because they sit on the same crate's facade. Wrong collapse hides the per-recommendation specificity the user needs to act on.

**Principle discipline.** When an option would violate `principles.md`, the option must either (a) be rejected with the principle cited as the reason, or (b) carry a paired option that evolves the principle, with rationale that cites the sprint/finding driving the evolution. Principles only evolve at sprint close (`/arch` Phase 7); the scoping pass surfaces *candidates* for evolution, not unilateral changes.

**Precedent discipline.** Each option cites a past Decision or sprint demonstrating the shape ("this is the same shape as Decision 26's variant-internal placement"). "Novel — no precedent" is a valid annotation but is itself a risk signal.

**Pre-identified load-bearing items.** These MUST appear as their own items, not as one-liners or as sub-bullets:

1. **Runtime bounded-context drift** — `io_trace.rs` + `trace.rs` (~25% of runtime LOC) violate the stated BC. Three options at minimum: relocate to int (BC stays); revise BC to admit observability inside runtime; split into a new diagnostics surface.
2. **`compile_to_module` return-shape facade silence** — backend facade names the function but does not pin the `(Arc<Jit>, HashMap<Symbol, *const u8>)` triple int composes into `Code::Jit`. Decision elevation candidate.
3. **`PlatformError` ↔ `ErrorLocation` adoption** — platform crate's loader/dispatch errors don't carry `ErrorLocation` per Decision 39. Cross-Decision-39 platform-side application; binds platform's public surface.
4. **Frontend `SymbolTables` alias tension** — alias used in `expand` and `check_form` signatures but constraint clarification is needed at int's instantiation site. Boundary-type tension between frontend's `SymbolTables` view and integration-layer `Code` carrier.

**Audit-related misalignments.** Treat as items in their own right:

5. **Two existing audits (typecheck, int) are post-dated by Decisions 38/39** — their target-direction sections are superseded; their current-state sections remain authoritative. Options for handling: annotate-and-defer; partial re-author (target-direction only); full re-pass.
6. **Two crates (runtime, platform) have no audit** — gap that the master design docs partly compensated for, but a fresh audit is needed before substance commitments on these surfaces can be made confidently.

## 6. Constraints

- No document changes other than `substance-scoping.md` itself.
- No FIXME filing during the scoping pass — recommendations *propose* filings, but execution waits for user acceptance.
- No Decision drafting during the scoping pass — recommendations *propose* Decision shape and binding, but the draft itself is a follow-on action.
- No code changes.
- In-session — cross-doc synthesis defeats subagent isolation, same rationale as the reconciliation plan.

## 7. Aggregate output expectations

A reader of `substance-scoping.md` should be able to answer five questions without further investigation:

1. **Are there bounded-context shifts in the queue?** Where, and how big?
2. **Are there principles that need evolving?** Which numbers, driven by which findings?
3. **Are there facades needing material redraft (vs editorial closure)?** Which sections, with what new signatures?
4. **Are there Decisions to supersede beyond the 38/39 lift?** Which numbers, replaced by what?
5. **Is the as-designed architecture viable as-is, or does it need adjustment?** A one-paragraph synthesis at the end of the document.

The fifth question is the executive summary. Place it as the document's opening *Synthesis* section so a reader who reads only the Synthesis + Description fields can navigate the rest by recommendation priority.

## 8. What this enables

After the scoping pass lands and the user accepts recommendations:

- The reconciliation plan adds a "substance wave" before Wave 1 (carrying the accepted Decision drafts, facade redrafts, BC shifts, principle evolutions) OR is confirmed adequate as-is.
- Each accepted recommendation becomes a concrete artefact change with rationale + consequences pre-written; the action skill executes mechanically.
- Sprint 64 scope candidates are concrete and pre-arbitrated; no item is "we should look at this."
- The next-pass audit (Wave 5 of the reconciliation plan) is scoped to validate the substance changes that landed, not to re-discover the same tensions from scratch.

## 9. Owner and next step

- Authored in-session by `/arch` (substance arbitration across crate boundaries is `/arch`'s prerogative).
- User reviews `substance-scoping.md` before any actioning. Per the project's review-before-enact discipline, no recommendation is enacted by `/arch` from the scoping pass alone.
- Outputs feed: revised reconciliation plan; Sprint 64 scope; deferred-audit triggers.

## 10. Effort and timing

- Cold read of inputs §3: 2–3 hours.
- Per-item analysis at the depth required: 15–30 minutes per item × 15–25 items = 4–10 hours.
- Synthesis section + cross-item sequencing: 1 hour.
- Total: one focused `/arch` session of 6–12 hours, possibly across two sittings if context fatigue is a risk.

The pass is `/arch`-solo work; it does not gate on `/sprint` scheduling and can be authored at the user's request as the next concrete step.

---

## Cross-references

- `design/arch/reconciliation-plan.md` — procedural plan this brief complements
- `design/arch/CLAUDE.md` — current decision log + canonical-doc pointer
- `design/arch/principles.md` — criteria the scoping pass cites
- `design/arch/bounded-contexts.md` — surface BCs the scoping pass tests against
- `design/arch/facades/{crate}.md` — facade specs the scoping pass tests against
- `design/{crate}/{crate}.md` — six master design docs (Sprint 63 deliverables; primary FIXME source)
- `audits/{crate}-20260423.md` — four existing audits (two with target-direction supersession)
- `sprints/fixmes/0001..0009-*.md` — already-filed FIXMEs (some master-doc inlines refine these)

— end of brief —
