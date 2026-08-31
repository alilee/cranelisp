#!/usr/bin/env python3
"""verify-role-wiring.py — the declared role set, its adapters, and its wiring agree.

Root `CLAUDE.md` §Roles declares twelve dispatched roles. Each one has to reach a
dispatch through four independent copies of the same fact: a contract in the
pinned `.agents` package, a Claude host adapter, a Copilot host adapter, and a
composition entry. Per-host adapter copies are the shape that has already
drifted twice (S65, S76), leaving Principles on disk invisible to the roles
applying them for whole sprints; the package converges every increment and can
rename or drop a role at any time.

Nothing about that agreement is structural — every copy is a separate file that
can be edited alone — so it is measured. This docstring is the single carrier of
the condition list; `tests/role_wiring.rs` proves each one detects, and cites
here rather than restating.

  W1  the declared role set equals the Claude adapter set equals the Copilot
      adapter set, and every declared role has a contract and a composition entry
  W2  each adapter names its own role, carries a model and effort allocation, and
      points at its role's contract
  W3  every skill named in the composition has a contract on disk
  W4  the subagent telemetry hooks, the dispatch transport, and the skills
      symlink are present
  W5  the Principle files on disk and the Principle index cite each other exactly,
      and each file's frontmatter number matches its filename
  W6  every role `sprints/METHOD.md` §1.1 obliges to read `design/arch/principles.md`
      first has that instruction in both of its host adapters
  W7  each Claude adapter's `model:` and `effort:` equal the definitive shared
      allocation in `.agents/agents/<role>.md` (Copilot adapters carry none)

W2 checks that an allocation is present; W7 checks that it is the one the package
allocated. Neither states a role-to-tier mapping. `.agents/CLAUDE.md` §Execution
tiers makes the frontmatter of `.agents/agents/<role>.md` the definitive
executable allocation and forbids a consumer remapping it, so reading that
carrier at check time single-sources the fact from its determinant rather than
copying a declaration. Until S120 this docstring asserted the opposite — that any
tier check here would copy the declaration under test. That held while the
allocation's only carriers were prose; it does not survive a determinant on disk,
and the transport prefers the consumer adapter, so an unobserved local remap
would execute. What W7 does not reach is the *executed* model and effort, which
are the dispatch row's.

W6 and W7 both read their subject out of the determinant rather than listing it
here: a second copy of the obliged set, or of the allocation, would drift from
its source exactly as an adapter can.

Usage:
    scripts/verify-role-wiring.py [ROOT]

ROOT defaults to the repository this script lives in. It is a parameter so the
detection proof (`tests/role_wiring.rs`) can run the identical command against a
scratch copy carrying a planted fault.
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

try:
    import tomllib
except ModuleNotFoundError:  # pragma: no cover - reported as a loud failure below
    tomllib = None

ROLES_TABLE_ROW = re.compile(r"^\|\s*`(?P<role>[a-z][a-z0-9-]*)`\s*\|")
FRONTMATTER_ENTRY = re.compile(r"^(?P<key>[A-Za-z_][A-Za-z0-9_-]*):\s*(?P<value>.*?)\s*$")
PRINCIPLE_FILE = re.compile(r"^(?P<num>\d{2})-[a-z0-9-]+\.md$")
PRINCIPLE_CITATION = re.compile(r"principles/(?P<file>\d{2}-[a-z0-9-]+\.md)")
NUMBER_FIELD = re.compile(r"^number:\s*(?P<num>\d{1,3})\s*$", re.MULTILINE)

PRINCIPLES_INDEX = "design/arch/principles.md"
# The clause in `sprints/METHOD.md` §1.1 that states the first-read obligation.
# Matching on the phrase rather than on a role list keeps METHOD the determinant.
FIRST_READ_CLAUSE = "read it first"
BACKTICKED = re.compile(r"`([a-z][a-z0-9-]*)`")


class Report:
    """Findings keyed by condition, plus the counters that prove work was done."""

    def __init__(self) -> None:
        self.findings: list[tuple[str, str]] = []
        self.counts: dict[str, int] = {}

    def fail(self, condition: str, detail: str) -> None:
        self.findings.append((condition, detail))


def read_text(path: Path) -> str:
    try:
        return path.read_text(errors="replace")
    except OSError:
        return ""


def frontmatter(path: Path) -> dict[str, str]:
    """The leading `---` fenced block as key/value pairs. Empty when absent."""
    lines = read_text(path).splitlines()
    if not lines or lines[0].strip() != "---":
        return {}
    fields: dict[str, str] = {}
    for line in lines[1:]:
        if line.strip() == "---":
            break
        m = FRONTMATTER_ENTRY.match(line)
        if m:
            fields[m.group("key")] = m.group("value")
    return fields


def declared_roles(root: Path, report: Report) -> list[str]:
    """Role names from the first table under root `CLAUDE.md` §Roles."""
    claude_md = root / "CLAUDE.md"
    if not claude_md.is_file():
        report.fail("W1", f"no root instruction file at {claude_md.name}")
        return []
    roles: list[str] = []
    in_section = False
    in_table = False
    for line in read_text(claude_md).splitlines():
        if line.startswith("## "):
            if in_table:
                break
            in_section = line.strip() == "## Roles"
            continue
        if not in_section:
            continue
        m = ROLES_TABLE_ROW.match(line)
        if m:
            in_table = True
            roles.append(m.group("role"))
        elif in_table and not line.startswith("|"):
            break
    if not roles:
        report.fail("W1", "the `## Roles` section of CLAUDE.md declares no role rows")
    return roles


def check_inventory(root: Path, roles: list[str], report: Report) -> None:
    """W1 — one role set, four carriers."""
    declared = set(roles)

    claude_dir = root / ".claude/agents"
    copilot_dir = root / ".github/agents"
    claude = {p.stem for p in claude_dir.glob("*.md")}
    copilot = {p.name[: -len(".agent.md")] for p in copilot_dir.glob("*.agent.md")}
    report.counts["claude adapters"] = len(claude)
    report.counts["copilot adapters"] = len(copilot)

    for role in sorted(declared - claude):
        report.fail("W1", f"role `{role}` is declared but has no Claude adapter at "
                          f".claude/agents/{role}.md")
    for name in sorted(claude - declared):
        report.fail("W1", f".claude/agents/{name}.md is an adapter for `{name}`, which "
                          f"root CLAUDE.md §Roles does not declare")
    for role in sorted(declared - copilot):
        report.fail("W1", f"role `{role}` is declared but has no Copilot adapter at "
                          f".github/agents/{role}.agent.md")
    for name in sorted(copilot - declared):
        report.fail("W1", f".github/agents/{name}.agent.md is an adapter for `{name}`, "
                          f"which root CLAUDE.md §Roles does not declare")

    composition = read_text(root / ".agents/skill-composition.toml")
    for role in roles:
        contract = root / f".agents/skills/{role}/SKILL.md"
        if not contract.is_file():
            report.fail("W1", f"role `{role}` has no contract at "
                              f".agents/skills/{role}/SKILL.md")
        if f"[roles.{role}]" not in composition:
            report.fail("W1", f"role `{role}` has no [roles.{role}] entry in "
                              f".agents/skill-composition.toml")


def check_adapters(root: Path, roles: list[str], report: Report) -> None:
    """W2 — each adapter names its own role, its allocation, and its contract."""
    for role in roles:
        contract = f".agents/skills/{role}/SKILL.md"

        claude = root / f".claude/agents/{role}.md"
        if claude.is_file():
            fields = frontmatter(claude)
            name = fields.get("name")
            if name != role:
                report.fail("W2", f".claude/agents/{role}.md declares `name: "
                                  f"{name or '<absent>'}`, not `{role}` — a dispatch of "
                                  f"`{role}` would select the wrong contract")
            for key in ("model", "effort"):
                if not fields.get(key):
                    report.fail("W2", f".claude/agents/{role}.md carries no `{key}:` "
                                      f"allocation; the transport refuses at dispatch "
                                      f"time, which is late")
            if contract not in read_text(claude):
                report.fail("W2", f".claude/agents/{role}.md does not name its contract "
                                  f"{contract}")

        copilot = root / f".github/agents/{role}.agent.md"
        if copilot.is_file():
            name = frontmatter(copilot).get("name")
            if name != role:
                report.fail("W2", f".github/agents/{role}.agent.md declares `name: "
                                  f"{name or '<absent>'}`, not `{role}`")
            if contract not in read_text(copilot):
                report.fail("W2", f".github/agents/{role}.agent.md does not name its "
                                  f"contract {contract}")


def check_allocation_parity(root: Path, roles: list[str], report: Report) -> None:
    """W7 — each Claude adapter's allocation equals the shared package's.

    The shared carrier is read here rather than mirrored, so this compares two
    copies of one fact instead of asserting a tier table of its own.
    """
    pairs = 0
    for role in roles:
        consumer = root / f".claude/agents/{role}.md"
        if not consumer.is_file():
            continue  # W1 owns an absent adapter; W7 would only repeat it
        shared = root / f".agents/agents/{role}.md"
        if not shared.is_file():
            report.fail("W7", f"role `{role}` has no shared allocation carrier at "
                              f".agents/agents/{role}.md, so .claude/agents/{role}.md's "
                              f"allocation has nothing definitive to agree with")
            continue

        allocated = frontmatter(shared)
        local = frontmatter(consumer)
        absent = [key for key in ("model", "effort") if not allocated.get(key)]
        if absent:
            report.fail("W7", f".agents/agents/{role}.md carries no "
                              f"{' or '.join(f'`{k}:`' for k in absent)} field; the "
                              f"definitive allocation for `{role}` is unreadable, and an "
                              f"unreadable determinant makes this comparison vacuous")
            continue

        for key in ("model", "effort"):
            if local.get(key) != allocated[key]:
                report.fail("W7", f".claude/agents/{role}.md allocates `{key}: "
                                  f"{local.get(key) or '<absent>'}` for `{role}`, but the "
                                  f"definitive shared allocation at .agents/agents/"
                                  f"{role}.md is `{key}: {allocated[key]}`. The transport "
                                  f"prefers the consumer adapter, so `{role}` would "
                                  f"execute remapped")
        pairs += 1
    report.counts["allocation pairs"] = pairs


def check_composed_skills(root: Path, report: Report) -> None:
    """W3 — every skill the composition names has a contract on disk."""
    path = root / ".agents/skill-composition.toml"
    if not path.is_file():
        report.fail("W3", "no .agents/skill-composition.toml")
        return
    if tomllib is None:
        report.fail("W3", "this interpreter has no `tomllib`; the composition cannot be "
                          "read. Python 3.11 or newer is required")
        return
    try:
        data = tomllib.loads(read_text(path))
    except tomllib.TOMLDecodeError as exc:
        report.fail("W3", f".agents/skill-composition.toml does not parse: {exc}")
        return

    named: set[str] = set(data.get("support", {}).get("skills", []))
    for entry in data.get("roles", {}).values():
        for key in ("always", "standing_documents"):
            named.update(entry.get(key, []))
    report.counts["composed skills"] = len(named)

    for skill in sorted(named):
        if not (root / f".agents/skills/{skill}/SKILL.md").is_file():
            report.fail("W3", f"the composition names skill `{skill}`, which has no "
                              f"contract at .agents/skills/{skill}/SKILL.md")


def check_dispatch_wiring(root: Path, report: Report) -> None:
    """W4 — telemetry hooks, transport, and the skills symlink."""
    settings = root / ".claude/settings.json"
    telemetry = ".agents/tools/subagent_telemetry.py"
    if not settings.is_file():
        report.fail("W4", ".claude/settings.json is absent, so no subagent lifecycle "
                          "hook is wired in this checkout")
    else:
        try:
            hooks = json.loads(read_text(settings)).get("hooks", {})
        except json.JSONDecodeError as exc:
            hooks = {}
            report.fail("W4", f".claude/settings.json does not parse: {exc}")
        for event in ("SubagentStart", "SubagentStop"):
            commands = [
                hook.get("command", "")
                for matcher in hooks.get(event, [])
                for hook in matcher.get("hooks", [])
                if hook.get("type") == "command"
            ]
            if not any(telemetry in c for c in commands):
                report.fail("W4", f".claude/settings.json declares no `{event}` command "
                                  f"hook running {telemetry}; dispatch rows for that "
                                  f"event are never written")

    for tool in (telemetry, ".agents/tools/claude_role.py"):
        if not (root / tool).is_file():
            report.fail("W4", f"{tool} is absent from the pinned package")

    skills = root / ".claude/skills"
    target = root / ".agents/skills"
    if not skills.is_symlink():
        report.fail("W4", ".claude/skills is not a symlink; role contracts do not "
                          "resolve for the Claude host")
    elif skills.resolve() != target.resolve():
        report.fail("W4", f".claude/skills resolves to {skills.resolve()}, not "
                          f"{target}")


def check_principles(root: Path, report: Report) -> None:
    """W5 — the Principle set on disk and the index that puts it in force agree."""
    index = root / "design/arch/principles.md"
    directory = root / "design/arch/principles"
    if not index.is_file():
        report.fail("W5", "no principle index at design/arch/principles.md")
        return

    on_disk = {p.name for p in directory.glob("*.md") if PRINCIPLE_FILE.match(p.name)}
    cited = set(PRINCIPLE_CITATION.findall(read_text(index)))
    report.counts["principles"] = len(on_disk)

    for name in sorted(on_disk - cited):
        report.fail("W5", f"design/arch/principles/{name} exists but the index does not "
                          f"cite it — the index is the single carrier of the set, so "
                          f"this Principle is not in force")
    for name in sorted(cited - on_disk):
        report.fail("W5", f"design/arch/principles.md cites {name}, which is not on disk")

    for name in sorted(on_disk):
        expected = PRINCIPLE_FILE.match(name).group("num")
        m = NUMBER_FIELD.search(read_text(directory / name))
        if not m:
            report.fail("W5", f"design/arch/principles/{name} has no `number:` field")
        elif m.group("num").zfill(2) != expected:
            report.fail("W5", f"design/arch/principles/{name} declares `number: "
                              f"{m.group('num')}`, which is not {expected}")


def first_read_roles(root: Path, roles: list[str], report: Report) -> list[str]:
    """The roles `sprints/METHOD.md` §1.1 obliges to read the principle index first.

    Read from METHOD rather than listed here: the obligation lives in that
    sentence, and a copy of the set in this script would drift from it exactly
    as an adapter can. An empty result is itself a finding — a check whose
    subject set is empty passes vacuously.
    """
    method = root / "sprints/METHOD.md"
    if not method.is_file():
        report.fail("W6", "no sprints/METHOD.md, so the first-read obligation has no "
                          "determinant to check the adapters against")
        return []

    declared = set(roles)
    named: list[str] = []
    for line in read_text(method).splitlines():
        if PRINCIPLES_INDEX not in line or FIRST_READ_CLAUSE not in line:
            continue
        for sentence in line.split(". "):
            if FIRST_READ_CLAUSE not in sentence:
                continue
            for role in BACKTICKED.findall(sentence):
                if role in declared and role not in named:
                    named.append(role)
            break
        break

    if not named:
        report.fail("W6", f"sprints/METHOD.md names no declared role as reading "
                          f"{PRINCIPLES_INDEX} first (looked for a sentence carrying both "
                          f"that path and \"{FIRST_READ_CLAUSE}\"). Either the obligation "
                          f"was dropped, or it was reworded and this check now has an "
                          f"empty subject set, which passes vacuously")
    return named


def check_first_read(root: Path, obliged: list[str], report: Report) -> None:
    """W6 — both host adapters of an obliged role carry the first-read instruction."""
    for role in obliged:
        for rel in (f".claude/agents/{role}.md", f".github/agents/{role}.agent.md"):
            adapter = root / rel
            if not adapter.is_file():
                continue  # W1 owns an absent adapter; W6 would only repeat it
            if PRINCIPLES_INDEX not in read_text(adapter):
                report.fail("W6", f"{rel} does not name {PRINCIPLES_INDEX}; "
                                  f"sprints/METHOD.md §1.1 obliges `{role}` to read the "
                                  f"principle index first, and this adapter drops the "
                                  f"instruction")


def main() -> int:
    root = Path(sys.argv[1]).resolve() if len(sys.argv) > 1 \
        else Path(__file__).resolve().parent.parent
    if not root.is_dir():
        print(f"ROLE WIRING: {root} is not a directory.")
        return 2

    report = Report()
    roles = declared_roles(root, report)
    report.counts["roles"] = len(roles)
    obliged = first_read_roles(root, roles, report)
    report.counts["first-read roles"] = len(obliged)
    check_inventory(root, roles, report)
    check_adapters(root, roles, report)
    check_allocation_parity(root, roles, report)
    check_composed_skills(root, report)
    check_dispatch_wiring(root, report)
    check_principles(root, report)
    check_first_read(root, obliged, report)

    for condition in ("W1", "W2", "W3", "W4", "W5", "W6", "W7"):
        group = [d for c, d in report.findings if c == condition]
        if group:
            print(f"\n=== {condition} ({len(group)}) ===")
            for detail in group:
                print(f"  {detail}")

    summary = ", ".join(f"{n} {label}" for label, n in report.counts.items())
    print(f"\n{root}: {summary}.")
    print(f"{len(report.findings)} finding(s).")
    return 1 if report.findings else 0


if __name__ == "__main__":
    sys.exit(main())
