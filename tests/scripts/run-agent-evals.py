#!/usr/bin/env python3
"""Run the local REPL-agent eval corpus against the `--features agent` binary.

Policy (tasks, graders, classifications, report contents) is QA's:
tests/plan/s122-evidence-delta.md §"Runnable eval corpus and policy". Usage and
fixture layout: tests/CLAUDE.md §"REPL-agent evals".

Each run is one fresh project, stdlib copy, process and log. Setup forms, the
`/ask` prompt and grader probes travel through ordinary REPL stdin, each
followed by a fresh random Int sentinel. Grading reads only the exact typed
result lines between consecutive sentinels, never agent prose.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import platform
import re
import secrets
import shutil
import signal
import statistics
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
FIXTURES = ROOT / "tests/fixtures/agent-evals"
DEFAULT_BINARY = ROOT / "target/agent/debug/cranelisp"
PROMPT_PREFIX = re.compile(r"^(?:\d+\+\d+ms; [^\s>]+> )+")
CHILD_FLAGS = ["--agent", "--no-cache", "--no-color"]
LIVE_PASSTHROUGH = ("ANTHROPIC_API_KEY", "CRANELISP_AGENT_KEY", "CRANELISP_AGENT_MODEL")
CREDENTIAL_VARS = ("ANTHROPIC_API_KEY", "CRANELISP_AGENT_KEY")


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def sha256_json(value) -> str:
    return sha256_bytes(json.dumps(value, sort_keys=True).encode())


def tree_hash(root: Path) -> str:
    h = hashlib.sha256()
    for path in sorted(p for p in root.rglob("*") if p.is_file()):
        h.update(str(path.relative_to(root)).encode() + b"\0" + sha256_file(path).encode() + b"\n")
    return h.hexdigest()


def git(*args: str) -> str:
    return subprocess.run(["git", "-C", str(ROOT), *args], capture_output=True, check=True).stdout.decode()


def load_task(task_id: str) -> tuple[dict, Path]:
    path = FIXTURES / "tasks" / f"{task_id}.json"
    return json.loads(path.read_text()), path


# --- grading ---------------------------------------------------------------


def int_line(value: int) -> str:
    return f":primitives/Int {value}"


def sentinel_indices(lines: list[str], value: int) -> list[int]:
    target = int_line(value)
    return [i for i, line in enumerate(lines) if line == target or line.endswith("> " + target)]


def observe_slot(lines: list[str]) -> dict:
    stripped = [PROMPT_PREFIX.sub("", line) for line in lines]
    typed = [s for s in stripped if s.startswith(":")]
    errors = [s for s in stripped if s.lower().startswith("error")]
    return {"typed": typed, "errors": errors, "lines": stripped}


def parse_log(text: str | None, scenario: str, target_symbol: str) -> dict:
    """Metrics from the agent JSONL log. Missing telemetry stays unavailable."""
    if text is None:
        return {"status": "missing", "metrics": "unavailable"}
    events = []
    for number, line in enumerate(text.splitlines(), 1):
        if not line.strip():
            continue
        try:
            event = json.loads(line)
        except json.JSONDecodeError:
            return {"status": "malformed", "detail": f"line {number} is not JSON", "metrics": "unavailable"}
        if not isinstance(event, dict) or not isinstance(event.get("event"), str):
            return {"status": "malformed", "detail": f"line {number} has no event", "metrics": "unavailable"}
        if event.get("scenario") != scenario:
            return {"status": "scenario_mismatch", "detail": f"line {number}", "metrics": "unavailable"}
        events.append(event)
    of = lambda kind: [e for e in events if e["event"] == kind]  # noqa: E731
    if not of("exchange"):
        return {"status": "no_exchange", "detail": "no exchange event; telemetry lost", "metrics": "unavailable"}
    pulls: dict[str, int] = {}
    for e in of("pull"):
        pulls[e.get("tool", "?")] = pulls.get(e.get("tool", "?"), 0) + 1
    target_submits = [e for e in of("submit") if e.get("symbol") == target_symbol]
    first = target_submits[0] if target_submits else None
    return {
        "status": "ok",
        "metrics": {
            "exchanges": len(of("exchange")),
            "submits": len(of("submit")),
            "repairs": len(of("repair")),
            "pulls_by_tool": pulls,
            "give_ups": [
                {k: e.get(k) for k in ("cause", "error_class", "steps_at_give_up")} for e in of("give_up")
            ],
            "steps_at_submit": [e.get("steps_at_submit") for e in of("submit")],
            "first_target_submit": (
                {"turn": first.get("turn"), "steps_at_submit": first.get("steps_at_submit")}
                if first and first.get("turn") is not None
                else "unavailable"
            ),
            "primer_hashes": sorted({e["primer_hash"] for e in events if "primer_hash" in e}),
            "harvest_len": [e["harvest_len"] for e in events if "harvest_len" in e],
            "tokens": "unknown",
            "cost": "unknown",
        },
    }


def grade(task: dict, plan: list[dict], stdout: str, process: dict, log: dict) -> dict:
    """Classify one run. `plan` lists each stdin step with the sentinel that follows it."""
    lines = stdout.splitlines()
    evidence: list[str] = []
    positions = []
    for step in plan:
        found = sentinel_indices(lines, step["sentinel"])
        if len(found) != 1:
            evidence.append(f"sentinel after {step['kind']} {step['id']} seen {len(found)} times")
        positions.append(found[0] if len(found) == 1 else None)
    framed = None not in positions and positions == sorted(positions)
    if None not in positions and positions != sorted(positions):
        evidence.append("sentinels out of order")

    observations = {"setup": [], "turn": [], "inject": [], "probe": []}
    if framed:
        start = 0
        for step, end in zip(plan, positions):
            slot = observe_slot(lines[start:end])
            start = end + 1
            if step["kind"] == "turn":
                observations["turn"] = slot["lines"]
            else:
                observations[step["kind"]].append({"id": step["id"], "typed": slot["typed"], "errors": slot["errors"]})

    def result(task_result: str, attribution: str | None) -> dict:
        return {
            "task_result": task_result,
            "attribution": attribution,
            "evidence": evidence,
            "observations": observations,
        }

    if process["timed_out"]:
        evidence.append("child killed at timeout; artifacts are partial")
        return result("ungradable", "unknown")
    if process["exit_code"] != 0:
        evidence.append(f"child exit {process['exit_code']} signal {process['signal']}")
        return result("ungradable", "unknown")
    if not framed:
        return result("ungradable", "harness")

    for expected, seen in zip(task["setup"], observations["setup"]):
        want = [] if expected["expect"] is None else [expected["expect"]]
        if seen["typed"] != want or (expected["expect"] is None and seen["errors"]):
            evidence.append(f"setup precondition failed: {expected['input']}")
            return result("ungradable", "unknown")

    probes = {p["id"]: p for p in observations["probe"]}
    for probe in observations["probe"]:
        if len(probe["typed"]) > 1:
            evidence.append(f"probe {probe['id']} produced {len(probe['typed'])} typed results")
            return result("ungradable", "harness")

    def value(probe_id: str) -> str | None:
        typed = probes[probe_id]["typed"]
        return typed[0] if typed else None

    for rule in task["not_completed_when"]:
        if value(rule["probe"]) == rule["equals"]:
            evidence.append(f"probe {rule['probe']} shows the pre-turn state")
            # A give_up follows a compiler rejection and can mask a provider
            # error, so it is evidence for a person, never an attribution.
            for g in log["metrics"]["give_ups"] if log["status"] == "ok" else []:
                evidence.append(
                    f"give_up recorded: cause={g['cause']} error_class={g['error_class']} "
                    f"steps_at_give_up={g['steps_at_give_up']}"
                )
            return result("not_completed", "unknown")

    wrong = [p for p in task["probes"] if p["expect"] is not None and value(p["id"]) != p["expect"]]
    if wrong:
        evidence.extend(f"probe {p['id']} expected {p['expect']!r} saw {value(p['id'])!r}" for p in wrong)
        return result("wrong_result", "unknown")
    return result("pass", None)


# --- launching -------------------------------------------------------------


def child_env(args, run_dir: Path, scenario: str, stub_script: Path | None) -> dict:
    env = {k: v for k, v in os.environ.items() if not k.startswith("CRANELISP_") and k not in CREDENTIAL_VARS}
    if args.provider != "stub":
        env.update({k: os.environ[k] for k in LIVE_PASSTHROUGH if k in os.environ})
    env.update(
        CRANELISP_LIB=str(run_dir / "lib"),
        CRANELISP_AGENT_PROVIDER=args.provider,
        CRANELISP_AGENT_LOG=str(run_dir / "agent-log.jsonl"),
        CRANELISP_AGENT_TRACE=str(run_dir / "agent-trace.txt"),
        CRANELISP_AGENT_SCENARIO=scenario,
    )
    if stub_script is not None:
        env["CRANELISP_AGENT_STUB_SCRIPT"] = str(stub_script)
    return env


def launch(binary: Path, run_dir: Path, env: dict, timeout: float) -> dict:
    """Run the child in its own process group; kill and reap the group on timeout."""
    started = time.monotonic()
    with open(run_dir / "stdin.txt", "rb") as fin, open(run_dir / "stdout.txt", "wb") as fout, open(
        run_dir / "stderr.txt", "wb"
    ) as ferr:
        child = subprocess.Popen(
            [str(binary), *CHILD_FLAGS, "--yes"],
            cwd=run_dir / "project",
            env=env,
            stdin=fin,
            stdout=fout,
            stderr=ferr,
            start_new_session=True,
        )
        timed_out = False
        try:
            code = child.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            timed_out = True
            os.killpg(child.pid, signal.SIGKILL)
            code = child.wait()
    group_residue = True
    try:
        os.killpg(child.pid, signal.SIGKILL)
    except ProcessLookupError:
        group_residue = False
    return {
        "exit_code": code,
        "signal": -code if code < 0 else None,
        "timed_out": timed_out,
        "group_residue_killed": group_residue,
        "duration_s": round(time.monotonic() - started, 3),
    }


def fresh_sentinels(count: int, avoid: set[str]) -> list[int]:
    values: list[int] = []
    while len(values) < count:
        value = 10**11 + secrets.randbelow(9 * 10**11)
        if value not in values and int_line(value) not in avoid:
            values.append(value)
    return values


def run_one(args, task: dict, task_path: Path, run_dir: Path, stub_text: str | None, inject: list[str], timeout: float):
    run_dir.mkdir(parents=True)
    (run_dir / "project").mkdir()
    shutil.copytree(ROOT / "stdlib", run_dir / "lib")
    stub_script = None
    if stub_text is not None:
        stub_script = run_dir / "stub-script.txt"
        stub_script.write_text(stub_text)

    steps = [{"kind": "setup", "id": str(i), "input": s["input"]} for i, s in enumerate(task["setup"])]
    steps.append({"kind": "turn", "id": "ask", "input": "/ask " + task["prompt"]})
    steps += [{"kind": "inject", "id": str(i), "input": line} for i, line in enumerate(inject)]
    steps += [{"kind": "probe", "id": p["id"], "input": p["input"]} for p in task["probes"]]
    avoid = {s.get("expect") for s in task["setup"]} | {p.get("expect") for p in task["probes"]}
    for step, sentinel in zip(steps, fresh_sentinels(len(steps), avoid)):
        step["sentinel"] = sentinel
    stdin = "".join(f"{s['input']}\n{s['sentinel']}\n" for s in steps)
    (run_dir / "stdin.txt").write_text(stdin)

    scenario = f"{task['id']}@v{task['version']}/{run_dir.name}"
    started_at = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    process = launch(args.binary, run_dir, child_env(args, run_dir, scenario, stub_script), timeout)

    log_path = run_dir / "agent-log.jsonl"
    log = parse_log(log_path.read_text() if log_path.exists() else None, scenario, task["target_symbol"])
    stdout = (run_dir / "stdout.txt").read_text(errors="replace")
    graded = grade(task, steps, stdout, process, log)
    api = "not_required" if task["api_review"] is None else "unreviewed"
    lib_sha256 = tree_hash(run_dir / "lib")
    shutil.rmtree(run_dir / "lib")
    return {
        "run_id": run_dir.name,
        "task_id": task["id"],
        "task_version": task["version"],
        "started_at": started_at,
        "process": process,
        "limits": {"timeout_s": timeout, "agent_turn_and_token_limits": "compiler built-in; not set by the runner"},
        "hashes": {
            "manifest": sha256_file(task_path),
            "prompt": sha256_bytes(task["prompt"].encode()),
            "probes": sha256_json(task["probes"]),
            "grader": sha256_file(Path(__file__)),
            "stub_script": sha256_bytes(stub_text.encode()) if stub_text is not None else None,
            "stdlib_copy_tree": lib_sha256,
        },
        **graded,
        "api_compliance": api,
        "api_review": task["api_review"],
        "complete_success": graded["task_result"] == "pass" and api == "not_required",
        "log": log,
        "artifacts": {
            str(p.relative_to(run_dir)): sha256_file(p) for p in sorted(run_dir.rglob("*")) if p.is_file()
        },
    }


# --- reporting -------------------------------------------------------------


def ollama_endpoint() -> str:
    # src/agent/provider.rs builds the client with rig-core 0.39.0
    # `ollama::Client::new(Nothing)`, which keeps the builder's fixed BASE_URL.
    # Only rig's `ProviderClient::from_env` reads OLLAMA_API_BASE_URL.
    endpoint = "http://localhost:11434 (rig-core ollama::Client::new default)"
    ignored = os.environ.get("OLLAMA_API_BASE_URL")
    if ignored:
        endpoint += f"; OLLAMA_API_BASE_URL={ignored} is set but not read"
    return endpoint


def provenance(args) -> dict:
    status = git("status", "--porcelain=v1", "--untracked-files=no")
    return {
        "runner": str(Path(__file__).relative_to(ROOT)),
        "runner_sha256": sha256_file(Path(__file__)),
        "repository_head": git("rev-parse", "HEAD").strip(),
        "dirty_paths": status.splitlines(),
        "dirty_diff_sha256": sha256_bytes(git("diff", "HEAD", "--binary").encode()),
        "binary": str(args.binary),
        "binary_sha256": sha256_file(args.binary),
        "binary_mtime": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(args.binary.stat().st_mtime)),
        "features_declared": ["agent"],
        "child_flags": CHILD_FLAGS + ["--yes"],
        "autonomy": "yes (auto-accept; no consent reads)",
        "cache_policy": "--no-cache; fresh project directory per run",
        "stdlib_tree_sha256": tree_hash(ROOT / "stdlib"),
        "cargo_lock_sha256": sha256_file(ROOT / "Cargo.lock"),
        "cargo_toml_sha256": sha256_file(ROOT / "Cargo.toml"),
        "platform": platform.platform(),
        "python": platform.python_version(),
        "provider": {
            "name": args.provider,
            "model": os.environ.get("CRANELISP_AGENT_MODEL") if args.provider != "stub" else None,
            "endpoint": {
                "stub": "in-process stub",
                "anthropic": "rig anthropic default",
                "ollama": ollama_endpoint(),
            }[args.provider],
            "credentials_present": args.provider != "stub" and credential_present(),
        },
    }


def summarize(runs: list[dict]) -> dict:
    by_task: dict[str, dict] = {}
    for run in runs:
        entry = by_task.setdefault(run["task_id"], {"runs": 0, "results": {}, "durations": []})
        entry["runs"] += 1
        entry["results"][run["task_result"]] = entry["results"].get(run["task_result"], 0) + 1
        entry["durations"].append(run["process"]["duration_s"])
    for entry in by_task.values():
        d = entry.pop("durations")
        entry["fractions"] = {k: f"{v}/{entry['runs']}" for k, v in entry["results"].items()}
        entry["duration_s"] = {"median": round(statistics.median(d), 3), "min": min(d), "max": max(d)}
    return by_task


def write_report(out: Path, report: dict) -> None:
    (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    rows = ["| run | task | result | attribution | exit | seconds | api | log |", "|---|---|---|---|---|---|---|---|"]
    for r in report["runs"]:
        rows.append(
            f"| {r['run_id']} | {r['task_id']} | {r['task_result']} | {r['attribution']} | "
            f"{r['process']['exit_code']} | {r['process']['duration_s']} | {r['api_compliance']} | {r['log']['status']} |"
        )
    checks = report.get("self_check")
    if checks:
        rows += ["", "| self-check | verdict | mismatches |", "|---|---|---|"]
        rows += [f"| {c['name']} | {'ok' if not c['mismatches'] else 'MISMATCH'} | {c['mismatches']} |" for c in checks]
    prov = report["provenance"]
    head = [
        f"# Agent eval report ({report['mode']})",
        "",
        f"Repository `{prov['repository_head']}` dirty paths {len(prov['dirty_paths'])}; "
        f"binary `{prov['binary']}` sha256 `{prov['binary_sha256'][:16]}…`; provider {prov['provider']['name']}.",
        "Stub results are harness checks, not a model baseline. Full provenance: report.json.",
        "",
    ]
    (out / "report.md").write_text("\n".join(head + rows) + "\n")


def prepare_out(out: Path) -> None:
    if out.exists() and any(out.iterdir()):
        sys.exit(f"refusing to reuse non-empty output directory {out}; attempts are never overwritten")
    out.mkdir(parents=True, exist_ok=True)


# --- self-check ------------------------------------------------------------


def lookup(record: dict, dotted: str):
    for part in dotted.split("."):
        record = record[part]
    return record


def mismatches(record: dict, expect: dict) -> list[str]:
    return [f"{k}: expected {v!r} saw {lookup(record, k)!r}" for k, v in expect.items() if lookup(record, k) != v]


def parser_case(case: dict) -> dict:
    task, _ = load_task(case["task"])
    text = (FIXTURES / "self-check" / case["transcript"]).read_text()
    for old, new in case.get("edits", []):
        if old not in text:
            raise SystemExit(f"parser case {case['name']}: edit target {old!r} absent")
        text = text.replace(old, new)
    kinds = ["setup"] * len(task["setup"]) + ["turn"] + ["probe"] * len(task["probes"])
    ids = [str(i) for i in range(len(task["setup"]))] + ["ask"] + [p["id"] for p in task["probes"]]
    plan = [{"kind": k, "id": i, "sentinel": s} for k, i, s in zip(kinds, ids, case["sentinels"])]
    scenario = "parser-case"
    log = parse_log(case["log"] if case["log"] is None else "\n".join(case["log"]), scenario, task["target_symbol"])
    process = {"exit_code": case.get("exit_code", 0), "signal": None, "timed_out": False}
    return {**grade(task, plan, text, process, log), "log": log}


def self_check(args) -> int:
    spec = json.loads((FIXTURES / "self-check/cases.json").read_text())
    checks, runs = [], []
    for case in spec["parser_cases"]:
        record = parser_case(case)
        checks.append({"name": "parser/" + case["name"], "mismatches": mismatches(record, case["expect"])})
    for case in spec["process_cases"]:
        task, path = load_task(case["task"])
        record = run_one(
            args,
            task,
            path,
            args.out / "runs" / f"self-{case['name']}",
            "\n".join(case["stub"]) + "\n",
            case.get("inject", []),
            case.get("timeout_s", args.timeout),
        )
        runs.append(record)
        checks.append({"name": "process/" + case["name"], "mismatches": mismatches(record, case["expect"])})
    report = {"mode": "self-check", "provenance": provenance(args), "self_check": checks, "runs": runs, "summary": summarize(runs)}
    write_report(args.out, report)
    failed = [c for c in checks if c["mismatches"]]
    for c in checks:
        print(("ok       " if not c["mismatches"] else "MISMATCH ") + c["name"], *c["mismatches"])
    print(f"{len(checks) - len(failed)}/{len(checks)} self-check cases agree; report {args.out / 'report.md'}")
    return 1 if failed else 0


def credential_present() -> bool:
    return any(os.environ.get(k) for k in CREDENTIAL_VARS)


def run(args) -> int:
    if args.provider != "stub" and not args.allow_live:
        sys.exit("a live provider needs --allow-live and a separately approved configuration and budget")
    # The product builds a dormant agent without these, which would grade as
    # not_completed and pollute the live denominators.
    if args.provider != "stub" and not os.environ.get("CRANELISP_AGENT_MODEL"):
        sys.exit("a live provider needs CRANELISP_AGENT_MODEL set")
    if args.provider == "anthropic" and not credential_present():
        sys.exit("--provider anthropic needs ANTHROPIC_API_KEY or CRANELISP_AGENT_KEY set")
    if args.provider == "stub" and args.stub_script is None:
        sys.exit("--provider stub needs --stub-script")
    stub_text = args.stub_script.read_text() if args.stub_script else None
    task_ids = args.task or sorted(p.stem for p in (FIXTURES / "tasks").glob("*.json"))
    prov = provenance(args)
    runs = []
    for task_id in task_ids:
        task, path = load_task(task_id)
        for repeat in range(1, args.repeats + 1):
            run_dir = args.out / "runs" / f"{task_id}-r{repeat}"
            record = run_one(args, task, path, run_dir, stub_text, [], args.timeout)
            record["repeat"] = repeat
            runs.append(record)
            print(f"{record['run_id']}: {record['task_result']} ({record['attribution']})")
            # Rewritten after every run so an interrupted paid series keeps its completed attempts.
            write_report(args.out, {"mode": "run", "provenance": prov, "runs": runs, "summary": summarize(runs)})
    print(f"report {args.out / 'report.md'}")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = parser.add_subparsers(dest="command", required=True)
    for name in ("run", "self-check"):
        p = sub.add_parser(name)
        p.add_argument("--binary", type=Path, default=DEFAULT_BINARY)
        p.add_argument("--out", type=Path, required=True, help="new or empty directory for this invocation")
        p.add_argument("--timeout", type=float, default=300.0, help="seconds per run before the process group is killed")
    run_p = sub.choices["run"]
    run_p.add_argument("--provider", choices=["stub", "anthropic", "ollama"], required=True)
    run_p.add_argument("--stub-script", type=Path)
    run_p.add_argument("--task", action="append", help="task id; default all")
    run_p.add_argument("--repeats", type=int, default=1)
    run_p.add_argument("--allow-live", action="store_true")
    run_p.add_argument("--autonomy", choices=["yes"], required=True, help="only --yes is supported (no consent reads)")
    args = parser.parse_args()
    if args.command == "self-check":
        args.provider = "stub"
    args.binary = args.binary.resolve()
    if not args.binary.is_file():
        sys.exit(f"missing binary {args.binary}; build it with: cargo build --features agent --target-dir target/agent")
    args.out = args.out.resolve()
    prepare_out(args.out)
    return self_check(args) if args.command == "self-check" else run(args)


if __name__ == "__main__":
    sys.exit(main())
