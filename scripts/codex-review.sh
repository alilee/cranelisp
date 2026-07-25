#!/usr/bin/env bash
# codex-review.sh — dispatch the /review role to the Codex CLI (headless).
#
# The Claude Code harness delegates change-set review to Codex for cross-model
# independence (see .claude/commands/review.md §Delegated execution and
# sprints/artefacts.md §II.3). This wrapper keeps every invocation uniform:
# read-only sandbox, the standard role-loading preamble, a change-set selector,
# and a structured verdict written to --out.
#
# Usage:
#   scripts/codex-review.sh (--uncommitted | --commit SHA | --base BRANCH)
#                           --brief FILE [--out FILE] [--title TITLE]
#
# The brief (composed by the invoking agent) names the crate-shaped scope,
# the design plan-of-record paths, the wave gate criteria, and test evidence.
# Codex runs sandboxed read-only: it cannot edit the tree, run cargo, or file
# FIXMEs — the invoking agent adjudicates the verdict and files FIXMEs from it.
#
# Note: `codex exec review`'s built-in selectors (--commit/--base/--uncommitted)
# are mutually exclusive with custom instructions, so this wrapper uses plain
# `codex exec` and states the change-set selector in the prompt; the read-only
# sandbox still permits the git reads the reviewer needs.

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SCHEMA="$REPO_ROOT/scripts/codex-review-schema.json"

selector=""
brief=""
out=""
title="cranelisp change-set review"

while [[ $# -gt 0 ]]; do
  case "$1" in
    --uncommitted)
      selector="The change set under review is the UNCOMMITTED state of the working tree: staged, unstaged, and untracked files. Enumerate it with \`git status --porcelain\` and read it with \`git diff HEAD\` plus the untracked files."
      shift ;;
    --commit)
      selector="The change set under review is commit $2. Read it with \`git show $2\`."
      shift 2 ;;
    --base)
      selector="The change set under review is everything on HEAD relative to base branch $2. Read it with \`git diff $2...HEAD\`."
      shift 2 ;;
    --brief)  brief="$2"; shift 2 ;;
    --out)    out="$2"; shift 2 ;;
    --title)  title="$2"; shift 2 ;;
    *) echo "unknown argument: $1" >&2; exit 2 ;;
  esac
done

if [[ -z "$selector" ]]; then
  echo "error: one of --uncommitted | --commit SHA | --base BRANCH is required" >&2
  exit 2
fi
if [[ -z "$brief" || ! -f "$brief" ]]; then
  echo "error: --brief FILE is required and must exist" >&2
  exit 2
fi
if [[ -z "$out" ]]; then
  out="$(mktemp -t codex-review-verdict.XXXXXX.json)"
fi

prompt="$(mktemp -t codex-review-prompt.XXXXXX.md)"
trap 'rm -f "$prompt"' EXIT

cat > "$prompt" <<PREAMBLE
You are the delegated external reviewer executing the Cranelisp \`/review\`
role ($title).

First read \`.claude/commands/review.md\` completely, then every file listed in
its \`# Imports\` block. Adopt that role's workflow, quality checks, findings
classification, and boundaries. You are running headless in a read-only
sandbox: you cannot edit files, run cargo, or file FIXMEs. Ignore that file's
"Delegated execution" section — it addresses the dispatching harness, not you.
Return your findings through the structured output schema; the invoking agent
files FIXMEs from them.

$selector

The review brief for this specific change set follows.

---

PREAMBLE
cat "$brief" >> "$prompt"

echo "codex-review: $(codex --version); title: $title; verdict -> $out" >&2

codex exec \
  -s read-only \
  --output-schema "$SCHEMA" \
  -o "$out" \
  - < "$prompt"

echo "codex-review: verdict written to $out" >&2
