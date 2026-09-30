#!/usr/bin/env python3
"""Check the local import graph, exact admissions, and portable source layout."""
from pathlib import Path
import argparse
import json
import re

ROOT = Path(__file__).resolve().parents[1]
_IMPORT_CACHE = {}


def code_only(text):
    """Blank nested Lean comments and strings while preserving line numbers."""
    out = []
    i = depth = 0
    string = False
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                depth += 1; out.extend('  '); i += 2
            elif text.startswith('-/', i):
                depth -= 1; out.extend('  '); i += 2
            else:
                out.append('\n' if text[i] == '\n' else ' '); i += 1
        elif string:
            out.append('\n' if text[i] == '\n' else ' ')
            if text[i] == '\\' and i + 1 < len(text):
                out.append(' '); i += 2
            else:
                if text[i] == '"': string = False
                i += 1
        elif text.startswith('/-', i):
            depth = 1; out.extend('  '); i += 2
        elif text.startswith('--', i):
            end = text.find('\n', i)
            end = len(text) if end < 0 else end
            out.extend(' ' * (end - i)); i = end
        elif text[i] == '"':
            string = True; out.append(' '); i += 1
        else:
            out.append(text[i]); i += 1
    if depth or string:
        raise ValueError('Unterminated comment or string')
    return ''.join(out)


def imports(path):
    if path not in _IMPORT_CACHE:
        _IMPORT_CACHE[path] = re.findall(r'^import\s+(\S+)', code_only(path.read_text()), re.M)
    return _IMPORT_CACHE[path]


def check():
    files = sorted((ROOT / 'ElevenSquare').rglob('*.lean')) + [ROOT / 'ElevenSquare.lean']
    modules = {'.'.join(p.relative_to(ROOT).with_suffix('').parts): p for p in files}
    found = []
    for p in files:
        code = code_only(p.read_text())
        _IMPORT_CACHE[p] = re.findall(r'^import\s+(\S+)', code, re.M)
        for word in ['axiom', 'admit', 'native_decide', 'sorryAx']:
            if re.search(r'\b' + word + r'\b', code):
                raise ValueError('Forbidden local proof form in ' + p.relative_to(ROOT).as_posix() + ': ' + word)
        for m in re.finditer(r'\bsorry\b', code):
            found.append({'path': p.relative_to(ROOT).as_posix(), 'line': code.count('\n', 0, m.start()) + 1})
        for dep in imports(p):
            if dep.startswith('ElevenSquare') and dep not in modules:
                raise ValueError('Missing local import: ' + dep)
    expected = json.loads((ROOT / 'verification/admissions.json').read_text())['sites']
    sort = lambda xs: sorted(xs, key=lambda x: (x['path'], x['line']))
    if sort(found) != sort(expected):
        raise ValueError('Admission inventory changed; review and update MISSING.md and admissions.json.')
    active = set(); done = set()
    def visit(name):
        if name in done: return
        if name in active: raise ValueError('Local import cycle: ' + name)
        active.add(name)
        for dep in imports(modules[name]):
            if dep in modules: visit(dep)
        active.remove(name); done.add(name)
    for name in modules: visit(name)
    return {'status': 'SOURCE_ASSEMBLY_PASS', 'local_modules': len(modules),
            'explicit_admissions': len(found), 'global_optimality_proved': False}


if __name__ == '__main__':
    print(json.dumps(check(), indent=2))
