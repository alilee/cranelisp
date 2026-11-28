#!/usr/bin/env python3
"""R18 source census: discarded witnesses and fabricated concrete defaults."""
import argparse
from pathlib import Path
import re

ROOTS = ('src', 'crates/cranelisp-types/src', 'crates/cranelisp-typecheck/src',
         'crates/cranelisp-backend/src')

# FIXME 0929: retained lenient conversion until its scheduled deletion.
ALLOW_LIST = (
    ('crates/cranelisp-types/src/mono_expr.rs',
     r'fn\s+lenient_from_expr\s*\(', 'function'),
)


def code_only(source):
    # Preserve offsets, newlines and code punctuation; erase comments/literals.
    raw_literal = re.compile(r'(?:br|r)(#*)"')
    char_literal = re.compile(r"'(?:\\.|[^'\\])'")
    out = list(source)
    i = 0
    while i < len(source):
        start = i
        if source.startswith('//', i):
            i = source.find('\n', i)
            if i < 0: i = len(source)
        elif source.startswith('/*', i):
            depth = 1
            i += 2
            while i < len(source) and depth:
                if source.startswith('/*', i): depth += 1; i += 2
                elif source.startswith('*/', i): depth -= 1; i += 2
                else: i += 1
        elif (raw := raw_literal.match(source, i)):
            end = '"' + raw[1]
            j = source.find(end, i + len(raw[0]))
            i = len(source) if j < 0 else j + len(end)
        elif source[i] == '"' or (source[i] == "'" and char_literal.match(source, i)):
            quote = source[i]
            i += 1
            while i < len(source):
                if source[i] == '\\': i += 2
                elif source[i] == quote: i += 1; break
                else: i += 1
        else:
            i += 1
            continue
        for k in range(start, min(i, len(source))):
            if out[k] != '\n': out[k] = ' '
    return ''.join(out)


def block_end(code, opening):
    depth = 1
    for i in range(opening + 1, len(code)):
        if code[i] == '{': depth += 1
        elif code[i] == '}':
            depth -= 1
            if not depth: return i + 1
    return len(code)


def production_code(path, source):
    code = code_only(source)
    spans = []
    # Inline and external cfg(test) modules are both removed from the census.
    for m in re.finditer(r'#\s*\[\s*cfg\s*\(\s*test\s*\)\s*\]\s*(?:#\[[^]]*\]\s*)*(?:pub(?:\([^)]*\))?\s+)?mod\s+\w+\s*\{', code):
        spans.append((m.start(), block_end(code, m.end() - 1)))
    chars = list(code)
    for start, end in spans:
        for i in range(start, end):
            if chars[i] != '\n': chars[i] = ' '
    return ''.join(chars)


PATTERNS = {
    'unchecked-call': r'(?:^|[;{}])\s*(?:\w+::)*ConcreteType\s*::\s*from_type\s*\((?:[^()]|\([^()]*\))*\)\s*(?:\.\s*ok\s*\(\))?\s*;',
    'discarded-witness': r'\blet\s+_\s*=\s*(?:\w+::)*ConcreteType\s*::\s*from_type\s*\([^;]*;',
    'erased-witness-error': r'\bConcreteType\s*::\s*from_type\s*\([^;]*?\.\s*unwrap_or_default\s*\(',
    'type-default': r'\b(?:ConcreteType|Type)\s*::\s*default\s*\(',
    'fallback-type': r'\.\s*(?:unwrap_or|unwrap_or_else|map_or|map_or_else)\s*\(\s*(?:\|[^|]*\|\s*)?(?:\{\s*)?(?:ConcreteType|Type)\s*::\s*(?!Var\b)',
    'typed-default': r'\blet\s+\w+\s*:\s*(?:ConcreteType|Type)\s*=\s*[^;]*?(?:Default\s*::\s*default\s*\(|\.\s*unwrap_or_default\s*\()',
}


def inspect(root):
    files = sorted({p for entry in ROOTS for p in (root / entry).rglob('*.rs')})
    excluded = set()
    for p in files:
        code = code_only(p.read_text())
        for m in re.finditer(r'#\s*\[\s*cfg\s*\(\s*test\s*\)\s*\]\s*(?:#\[[^]]*\]\s*)*(?:pub(?:\([^)]*\))?\s+)?mod\s+(\w+)\s*;', code):
            base = p.parent if p.name in ('lib.rs', 'main.rs', 'mod.rs') else p.with_suffix('')
            excluded.add(base / (m[1] + '.rs'))
            excluded.update((base / m[1]).rglob('*.rs'))
    findings = []
    used_allowances = set()
    for path in files:
        if path in excluded: continue
        relative = path.relative_to(root).as_posix()
        code = production_code(path.relative_to(root), path.read_text())
        allowances = []
        for index, (allowed_path, scope, kind) in enumerate(ALLOW_LIST):
            if relative != allowed_path: continue
            for site in re.finditer(scope, code):
                end = (block_end(code, code.find('{', site.end()))
                       if kind == 'function' else site.end())
                allowances.append((index, site.start(), end))
        for label, pattern in PATTERNS.items():
            for match in re.finditer(pattern, code, re.S):
                allowed = [index for index, start, end in allowances
                           if label == 'fallback-type'
                           and start <= match.start() and match.end() <= end]
                if allowed:
                    used_allowances.update(allowed)
                    continue
                line = code[:match.start()].count('\n') + 1
                findings.append(f'{path.relative_to(root)}:{line}: {label}')
    for index, (path, scope, _) in enumerate(ALLOW_LIST):
        if index not in used_allowances:
            findings.append(f'{path}: stale-allow-list ({scope})')
    return findings


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, required=True)
    args = parser.parse_args()
    findings = inspect(args.root)
    print('\n'.join(findings) if findings else 'R18 census: no unapproved discarded witness or type default')
    raise SystemExit(bool(findings))
