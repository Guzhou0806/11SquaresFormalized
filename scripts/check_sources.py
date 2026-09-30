#!/usr/bin/env python3
"""Check the local import graph, exact admissions, and portable source layout."""
from pathlib import Path
import argparse
import hashlib
import json
import os
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


def check(use_cache=False):
    # The standalone audit and --fresh always rescan. Resumed compilations may
    # reuse lexical results only when both the scanner and source bytes match.
    cache_path = ROOT / '.verification/source-scan.json'
    scanner = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    cache = {}
    if use_cache and cache_path.is_file():
        try:
            saved = json.loads(cache_path.read_text())
            if saved.get('scanner') == scanner:
                cache = saved.get('files', {})
        except (ValueError, OSError):
            pass
    next_cache = {}
    files = sorted((ROOT / 'ElevenSquare').rglob('*.lean')) + sorted((ROOT / 'Sqpack').rglob('*.lean')) + [ROOT / 'ElevenSquare.lean', ROOT / 'Sqpack.lean']
    modules = {'.'.join(p.relative_to(ROOT).with_suffix('').parts): p for p in files}
    found = []
    for p in files:
        rel = p.relative_to(ROOT).as_posix()
        data = p.read_bytes()
        digest = hashlib.sha256(data).hexdigest()
        info = cache.get(rel, {})
        if info.get('sha256') != digest:
            code = code_only(data.decode())
            for word in ['axiom', 'admit', 'native_decide', 'sorryAx']:
                if re.search(r'\b' + word + r'\b', code):
                    raise ValueError('Forbidden local proof form in ' + rel + ': ' + word)
            info = {'sha256': digest,
                    'imports': re.findall(r'^import\s+(\S+)', code, re.M),
                    'admissions': [code.count('\n', 0, m.start()) + 1
                                   for m in re.finditer(r'\bsorry\b', code)]}
        _IMPORT_CACHE[p] = info['imports']
        next_cache[rel] = info
        found.extend({'path': rel, 'line': line} for line in info['admissions'])
        for dep in imports(p):
            if dep.startswith(('ElevenSquare', 'Sqpack')) and dep not in modules:
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
    if use_cache:
        cache_path.parent.mkdir(exist_ok=True)
        temporary = cache_path.with_name(cache_path.name + f'.{os.getpid()}.tmp')
        temporary.write_text(json.dumps({'scanner': scanner, 'files': next_cache}))
        temporary.replace(cache_path)
    return {'status': 'SOURCE_ASSEMBLY_PASS', 'local_modules': len(modules),
            'explicit_admissions': len(found), 'global_optimality_proved': False}


if __name__ == '__main__':
    print(json.dumps(check(), indent=2))
