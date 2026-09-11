#!/usr/bin/env python3
"""Verify the shared consumer contract, then Cranelisp's local role wiring.

The pinned package's offline ``check_consumer.py`` is the first structural gate.
It owns declaration validation, Claude adapter identity and allocation parity,
package contracts and composition, link topology, manifests, and submodule
wiring. A failure stops this script before any local prerequisite can mask it.

The remaining conditions belong to this repository:

  W1  root ``CLAUDE.md`` declares the same subordinate roles as
      ``.agents-consumer.toml``, and Copilot exposes exactly that set
  W2  each Copilot adapter names its role and shared contract
  W3  lifecycle telemetry, provider-routing guard, and dispatch transports are
      wired; the PreToolUse guard is unfiltered
  W4  Principle files and their canonical index cite each other exactly, and
      each file's frontmatter number matches its filename
  W5  every role ``sprints/METHOD.md`` obliges to read the Principle index first
      carries that instruction in both host adapters

The subjects for W1 and W5 are read from their determinants rather than copied
here. ``tests/role_wiring.rs`` proves the shared integration and every local
condition detect planted faults.

Usage:
    scripts/verify-role-wiring.py [ROOT]
"""

from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path

try:
    import tomllib
except ModuleNotFoundError:  # pragma: no cover - shared checker reports this first
    tomllib = None

ROLES_TABLE_ROW = re.compile(r"^\|\s*`(?P<role>[a-z][a-z0-9-]*)`\s*\|")
FRONTMATTER_ENTRY = re.compile(r"^(?P<key>[A-Za-z_][A-Za-z0-9_-]*):\s*(?P<value>.*?)\s*$")
PRINCIPLE_FILE = re.compile(r"^(?P<num>\d{2})-[a-z0-9-]+\.md$")
PRINCIPLE_CITATION = re.compile(r"principles/(?P<file>\d{2}-[a-z0-9-]+\.md)")
NUMBER_FIELD = re.compile(r"^number:\s*(?P<num>\d{1,3})\s*$", re.MULTILINE)

PRINCIPLES_INDEX = "design/arch/principles.md"
FIRST_READ_CLAUSE = "read it first"
BACKTICKED = re.compile(r"`([a-z][a-z0-9-]*)`")


class Report:
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
    lines = read_text(path).splitlines()
    if not lines or lines[0].strip() != "---":
        return {}
    fields: dict[str, str] = {}
    for line in lines[1:]:
        if line.strip() == "---":
            break
        match = FRONTMATTER_ENTRY.match(line)
        if match:
            fields[match.group("key")] = match.group("value")
    return fields


def run_consumer_check(root: Path) -> int:
    """Run the package-owned gate first and forward its concise report."""
    checker = root / ".agents/tools/check_consumer.py"
    if not checker.is_file():
        print(f"consumer-check-missing {checker}: the pinned checker cannot run")
        return 1
    try:
        run = subprocess.run(
            [sys.executable, str(checker), "--root", str(root)],
            capture_output=True,
            text=True,
            check=False,
        )
    except OSError as error:
        print(f"consumer-check-unrunnable {checker}: {error}")
        return 1
    if run.stdout.strip():
        print(run.stdout.rstrip())
    if run.stderr.strip():
        print(run.stderr.rstrip(), file=sys.stderr)
    return run.returncode


def declared_roles(root: Path, report: Report) -> list[str]:
    path = root / "CLAUDE.md"
    if not path.is_file():
        report.fail("W1", "no root instruction file at CLAUDE.md")
        return []
    roles: list[str] = []
    in_section = False
    in_table = False
    for line in read_text(path).splitlines():
        if line.startswith("## "):
            if in_table:
                break
            in_section = line.strip() == "## Roles"
            continue
        if not in_section:
            continue
        match = ROLES_TABLE_ROW.match(line)
        if match:
            in_table = True
            roles.append(match.group("role"))
        elif in_table and not line.startswith("|"):
            break
    if not roles:
        report.fail("W1", "the `## Roles` section of CLAUDE.md declares no role rows")
    return roles


def consumer_roles(root: Path) -> list[str]:
    """The package checker has already validated this declaration."""
    if tomllib is None:
        return []
    data = tomllib.loads(read_text(root / ".agents-consumer.toml"))
    return data["roles"]["dispatched"]


def check_inventory(root: Path, prose_roles: list[str], report: Report) -> None:
    """W1 — local prose, machine declaration, and Copilot inventory agree."""
    prose = set(prose_roles)
    machine = set(consumer_roles(root))
    copilot_dir = root / ".github/agents"
    copilot = {p.name[: -len(".agent.md")] for p in copilot_dir.glob("*.agent.md")}
    report.counts["subordinate roles"] = len(machine)
    report.counts["Copilot adapters"] = len(copilot)

    for role in sorted(machine - prose):
        report.fail("W1", f".agents-consumer.toml dispatches `{role}`, but root "
                    "CLAUDE.md §Roles has no row for it")
    for role in sorted(prose - machine):
        report.fail("W1", f"root CLAUDE.md §Roles declares `{role}`, but "
                    ".agents-consumer.toml does not dispatch it")
    for role in sorted(machine - copilot):
        report.fail("W1", f"role `{role}` is dispatched but has no Copilot adapter at "
                    f".github/agents/{role}.agent.md")
    for role in sorted(copilot - machine):
        report.fail("W1", f".github/agents/{role}.agent.md exposes `{role}`, which "
                    ".agents-consumer.toml does not dispatch")


def check_copilot_adapters(root: Path, roles: list[str], report: Report) -> None:
    """W2 — Copilot adapter identity and contract references."""
    for role in roles:
        relative = f".github/agents/{role}.agent.md"
        path = root / relative
        if not path.is_file():
            continue  # W1 owns absence
        name = frontmatter(path).get("name")
        if name != role:
            report.fail("W2", f"{relative} declares `name: {name or '<absent>'}`, not "
                        f"`{role}`")
        contract = f".agents/skills/{role}/SKILL.md"
        if contract not in read_text(path):
            report.fail("W2", f"{relative} does not name its contract {contract}")


def command_hooks(hooks: dict, event: str) -> list[tuple[dict, str]]:
    entries = hooks.get(event, [])
    if not isinstance(entries, list):
        return []
    return [
        (matcher, hook.get("command", ""))
        for matcher in entries
        if isinstance(matcher, dict)
        for hook in matcher.get("hooks", [])
        if isinstance(hook, dict) and hook.get("type") == "command"
    ]


def check_dispatch_wiring(root: Path, report: Report) -> None:
    """W3 — repository hook policy, transports, and skills exposure."""
    settings = root / ".claude/settings.json"
    hooks: dict = {}
    if not settings.is_file():
        report.fail("W3", ".claude/settings.json is absent, so dispatch hooks are unwired")
    else:
        try:
            parsed = json.loads(read_text(settings))
        except json.JSONDecodeError as error:
            report.fail("W3", f".claude/settings.json does not parse: {error}")
        else:
            candidate = parsed.get("hooks") if isinstance(parsed, dict) else None
            if isinstance(candidate, dict):
                hooks = candidate
            else:
                report.fail("W3", ".claude/settings.json carries no `hooks` object")

    telemetry = ".agents/tools/subagent_telemetry.py"
    for event in ("SubagentStart", "SubagentStop"):
        commands = command_hooks(hooks, event)
        if not any(telemetry in command for _, command in commands):
            report.fail("W3", f".claude/settings.json declares no `{event}` command "
                        f"hook running {telemetry}")

    guard = ".agents/tools/guard_dispatch.py"
    guard_hooks = [
        matcher for matcher, command in command_hooks(hooks, "PreToolUse")
        if guard in command
    ]
    if not guard_hooks:
        report.fail("W3", ".claude/settings.json declares no `PreToolUse` command hook "
                    f"running {guard}")
    elif not any("matcher" not in entry for entry in guard_hooks):
        report.fail("W3", f"the `PreToolUse` hook running {guard} is filtered by a "
                    "tool-name matcher and cannot guard every native dispatch")

    tools = (
        telemetry,
        guard,
        ".agents/tools/codex_role.py",
        ".agents/tools/claude_role.py",
    )
    for tool in tools:
        if not (root / tool).is_file():
            report.fail("W3", f"{tool} is absent from the pinned package")

def check_principles(root: Path, report: Report) -> None:
    """W4 — the Principle set and its canonical index agree."""
    index = root / PRINCIPLES_INDEX
    directory = root / "design/arch/principles"
    if not index.is_file():
        report.fail("W4", f"no principle index at {PRINCIPLES_INDEX}")
        return

    on_disk = {p.name for p in directory.glob("*.md") if PRINCIPLE_FILE.match(p.name)}
    cited = set(PRINCIPLE_CITATION.findall(read_text(index)))
    report.counts["principles"] = len(on_disk)
    for name in sorted(on_disk - cited):
        report.fail("W4", f"design/arch/principles/{name} exists but the index does not "
                    "cite it")
    for name in sorted(cited - on_disk):
        report.fail("W4", f"{PRINCIPLES_INDEX} cites {name}, which is not on disk")
    for name in sorted(on_disk):
        expected = PRINCIPLE_FILE.match(name).group("num")
        match = NUMBER_FIELD.search(read_text(directory / name))
        if not match:
            report.fail("W4", f"design/arch/principles/{name} has no `number:` field")
        elif match.group("num").zfill(2) != expected:
            report.fail("W4", f"design/arch/principles/{name} declares `number: "
                        f"{match.group('num')}`, not {expected}")


def first_read_roles(root: Path, roles: list[str], report: Report) -> list[str]:
    """Read METHOD §1.1's first-read subject set without copying it."""
    method = root / "sprints/METHOD.md"
    if not method.is_file():
        report.fail("W5", "no sprints/METHOD.md, so the first-read determinant is absent")
        return []
    declared = set(roles)
    named: list[str] = []
    for line in read_text(method).splitlines():
        if PRINCIPLES_INDEX not in line or FIRST_READ_CLAUSE not in line:
            continue
        for sentence in line.split(". "):
            if FIRST_READ_CLAUSE in sentence:
                for role in BACKTICKED.findall(sentence):
                    if role in declared and role not in named:
                        named.append(role)
                break
        break
    if not named:
        report.fail("W5", f"sprints/METHOD.md names no dispatched role as reading "
                    f"{PRINCIPLES_INDEX} first")
    return named


def check_first_read(root: Path, obliged: list[str], report: Report) -> None:
    """W5 — both host adapters carry every applicable first-read instruction."""
    for role in obliged:
        for relative in (f".claude/agents/{role}.md", f".github/agents/{role}.agent.md"):
            path = root / relative
            if path.is_file() and PRINCIPLES_INDEX not in read_text(path):
                report.fail("W5", f"{relative} does not name {PRINCIPLES_INDEX}; "
                            f"sprints/METHOD.md §1.1 obliges `{role}` to read it first")


def main() -> int:
    root = (Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).parent.parent).resolve()
    if not root.is_dir():
        print(f"ROLE WIRING: {root} is not a directory.")
        return 2

    consumer_status = run_consumer_check(root)
    if consumer_status != 0:
        return consumer_status

    report = Report()
    prose_roles = declared_roles(root, report)
    machine_roles = consumer_roles(root)
    check_inventory(root, prose_roles, report)
    check_copilot_adapters(root, machine_roles, report)
    check_dispatch_wiring(root, report)
    check_principles(root, report)
    obliged = first_read_roles(root, machine_roles, report)
    report.counts["first-read roles"] = len(obliged)
    check_first_read(root, obliged, report)

    for condition in ("W1", "W2", "W3", "W4", "W5"):
        group = [detail for found, detail in report.findings if found == condition]
        if group:
            print(f"\n=== {condition} ({len(group)}) ===")
            for detail in group:
                print(f"  {detail}")

    summary = ", ".join(f"{count} {label}" for label, count in report.counts.items())
    print(f"\n{root}: {summary}; {len(report.findings)} local finding(s).")
    return 1 if report.findings else 0


if __name__ == "__main__":
    raise SystemExit(main())
