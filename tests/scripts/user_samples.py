#!/usr/bin/env python3
"""M-3 maintenance check; metadata contract: tests/AGENTS.md."""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

REPO = Path(__file__).resolve().parents[2]
ANSI = re.compile(r"\x1b\[[0-9;?]*[a-zA-Z]")
PROMPT = re.compile(r"\d+\+\d+ms; [^\s>]+> | {5,}\.\.\.")
INPUT = re.compile(r"^(?:> |\d+\+\d+ms; [^\s>]+> |[^\s>]+> |\.\.\. )(.*)$")
FENCE = re.compile(r"^ {0,3}(`{3,}|~{3,})(.*)$")
META = re.compile(r"^\s*<!-- sample: (.+) -->\s*$")


class SampleError(Exception):
    pass


def census(root):
    blocks = []
    paths = sorted(root.rglob('*.md'))
    if not paths:
        raise SampleError(f"no Markdown documents under {root}")
    for path in paths:
        lines = path.read_text().splitlines()
        i = 0
        while i < len(lines):
            opening = FENCE.match(lines[i])
            if not opening:
                i += 1
                continue
            where = f"{path}:{i + 1}"
            annotation = META.match(lines[i - 1]) if i else None
            if not annotation:
                raise SampleError(f"{where}: unclassified fence")
            try:
                meta = json.loads(annotation[1])
            except json.JSONDecodeError as error:
                raise SampleError(f"{where}: invalid sample JSON: {error}") from error
            if not isinstance(meta, dict) or meta.get('kind') not in ('repl', 'definition', 'illustrative'):
                raise SampleError(f"{where}: invalid classification")
            if set(meta) - {'kind', 'group', 'files', 'reason'}:
                raise SampleError(f"{where}: unknown metadata field")
            if 'group' in meta and (not isinstance(meta['group'], str) or not meta['group'].strip()):
                raise SampleError(f"{where}: group must be a nonempty string")
            if meta['kind'] == 'illustrative' and (not isinstance(meta.get('reason'), str) or not meta['reason'].strip()):
                raise SampleError(f"{where}: illustrative fence needs a reason")
            if not isinstance(meta.get('files', {}), dict):
                raise SampleError(f"{where}: files must map paths to source strings")
            body = []
            i += 1
            while i < len(lines):
                closing = FENCE.match(lines[i])
                if closing and closing[1][0] == opening[1][0] and len(closing[1]) >= len(opening[1]) and not closing[2].strip():
                    break
                body.append(lines[i])
                i += 1
            if i == len(lines):
                raise SampleError(f"{where}: unclosed fence")
            blocks.append((path, where, meta, body))
            i += 1
    print(f"Census: {len(paths)} documents, {len(blocks)} classified fences")
    return blocks


def normalized(text, root):
    return ANSI.sub('', text).replace('\r', '').replace(str(root), '{{ROOT}}').strip('\n')


def execute(blocks, binary):
    groups = {}
    for path, where, meta, body in blocks:
        if meta['kind'] != 'illustrative':
            groups.setdefault((path, meta.get('group', where)), []).append((where, meta, body))
    for (_, group), members in groups.items():
        with tempfile.TemporaryDirectory(prefix='cranelisp-user-samples-') as temporary:
            root = Path(temporary)
            files = {}
            turns = []
            startup = None
            for where, meta, body in members:
                for name, source in meta.get('files', {}).items():
                    rel = Path(name)
                    if (rel.is_absolute() or not rel.parts or '..' in rel.parts
                            or any(part.startswith('.') for part in rel.parts)
                            or rel.name == 'prelude.cl' or not isinstance(source, str)):
                        raise SampleError(f"{where}: unsafe fixture path or source: {name}")
                    if name in files and files[name] != source:
                        raise SampleError(f"{where}: conflicting fixture {name}")
                    files[name] = source
                if meta['kind'] == 'definition':
                    turns.extend([line, None, where] for line in body)
                    continue
                first = True
                for line in body:
                    match = INPUT.match(line)
                    if match:
                        turns.append([match[1], [], where])
                        first = False
                    elif first:
                        if turns:
                            raise SampleError(f"{where}: output-only fragment or startup inside group")
                        if startup is None:
                            startup = []
                        startup.append(line)
                    else:
                        turns[-1][1].append(line)
                if first:
                    raise SampleError(f"{where}: REPL block has no input; classify output-only fragments as illustrative")
            if not turns:
                raise SampleError(f"{group}: executable group has no input")
            for name, source in files.items():
                dest = root / name
                dest.parent.mkdir(parents=True, exist_ok=True)
                dest.write_text(source)
            # Isolate compiler switches and user-level configuration. In particular,
            # no provider/key from the caller may activate an external agent.
            env = {k: v for k, v in os.environ.items() if not k.startswith('CRANELISP_')}
            env.update(CRANELISP_LIB=str(REPO / 'stdlib'),
                       CRANELISP_PLATFORM_PATH=str(binary.parent),
                       XDG_CONFIG_HOME=str(root / '.config'))
            result = subprocess.run([str(binary)], cwd=root, env=env,
                                    input='\n'.join(t[0] for t in turns) + '\n',
                                    text=True, stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT, timeout=60)
            output = ANSI.sub('', result.stdout).replace('\r', '')
            parts = PROMPT.split(output)
            if result.returncode != 0 or len(parts) != len(turns) + 2:
                raise SampleError(f"{group}: compiler exit/prompt mismatch ({result.returncode}, "
                                  f"{len(parts)-1} prompts for {len(turns)} inputs)\n{output}")
            if startup is not None and normalized(parts[0], root) != normalized('\n'.join(startup), root):
                raise SampleError(f"{group}: startup mismatch\nactual:\n{parts[0]}")
            for (source, expected, where), actual in zip(turns, parts[1:-1]):
                actual = normalized(actual, root)
                if expected is None:
                    if re.search(r'(?im)^\s*(?:Error:|(?:parse|type|module|codegen) error\b|Cannot evaluate:|command not yet available)', actual):
                        raise SampleError(f"{where}: definition failed: {source}\n{actual}")
                elif actual != normalized('\n'.join(expected), root):
                    raise SampleError(f"{where}: expected output mismatch for {source!r}\n"
                                      f"expected:\n{chr(10).join(expected)}\nactual:\n{actual}")
            print(f"PASS {group}: {len(turns)} input lines")
    print(f"Executed {len(groups)} fresh groups")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--docs', type=Path, default=REPO / 'user')
    parser.add_argument('--binary', type=Path, default=REPO / 'target/debug/cranelisp')
    parser.add_argument('--census-only', action='store_true')
    args = parser.parse_args()
    try:
        blocks = census(args.docs.resolve())
        if not args.census_only:
            execute(blocks, args.binary.resolve())
    except (SampleError, OSError, subprocess.TimeoutExpired) as error:
        print(f"USER SAMPLE CHECK FAILED: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())
