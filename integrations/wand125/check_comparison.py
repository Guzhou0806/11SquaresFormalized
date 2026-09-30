#!/usr/bin/env python3
"""Recheck upstream provenance and finite case correspondence; not a Lean proof."""
import ast
import hashlib
import itertools
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


def require(ok, message):
    if not ok:
        raise ValueError(message)


def literal_list(source, name):
    match = re.search(r'def ' + re.escape(name) + r' : List ℕ := (\[[^\n]*\])', source)
    require(match is not None, 'Missing literal list: ' + name)
    return ast.literal_eval(match[1])


def array(source, name):
    chunks = re.findall(r'def ' + name + r'Chunk(\d+) : Array \([^\n]+\) := #\[(.*?)\n\]', source, re.S)
    require(bool(chunks), 'Missing array chunks: ' + name)
    chunks.sort(key=lambda pair: int(pair[0]))
    require([int(i) for i, _ in chunks] == list(range(len(chunks))), 'Noncontiguous chunks: ' + name)
    assembled = re.search(r'def ' + name + r' : Array \([^\n]+\) := ([^\n]+)', source)
    require(assembled is not None, 'Missing assembly: ' + name)
    require(assembled[1].split(' ++ ') == [name + 'Chunk' + i for i, _ in chunks], 'Changed assembly: ' + name)
    return sum((ast.literal_eval('[' + text + ']') for _, text in chunks), [])


def check():
    provenance = json.loads((HERE / 'provenance.json').read_text())
    for branch, snapshot in provenance['snapshots'].items():
        for rel, digest in snapshot['files'].items():
            path = HERE / branch / rel
            require(path.is_file() and hashlib.sha256(path.read_bytes()).hexdigest() == digest,
                    'Upstream snapshot changed: ' + branch + '/' + rel)
    source = (ROOT / 'ElevenSquare/Pending/S06_Data.lean').read_text()
    interface = (HERE / 'split/lean/Sqpack/S11Opt/Split/Interface.lean').read_text()
    cases = array(source, 'recordedCaseTuples')
    canonical = [list(j) for j in itertools.combinations(range(16), 11)
                 if j <= tuple(sorted(15 - x for x in j))]
    require(cases == canonical and len(cases) == 2184, 'Canonical case order changed')
    families = {name: array(source, name + 'Array') for name in ['baseline', 'prior', 'returned', 'candidate']}
    for name, upstream in [('prior', 'priorIdx'), ('returned', 'returnedIdx'), ('candidate', 'candIdx')]:
        require(families[name] == literal_list(interface, upstream), 'Family differs: ' + name)
    generic = literal_list(interface, 'genericIdx')
    require(len(generic) == 27 and set(generic) <= set(families['baseline']), 'Generic/baseline mismatch')
    require(sorted(sum(families.values(), [])) == list(range(2184)), 'Families do not partition the cases')
    fields = {}
    for n in [3, 6, 19]:
        text = (ROOT / f'Sqpack/S11Opt/F{n:02d}/Data.lean').read_text()
        fields[n] = {key: literal_list(text, key) for key in ['supp', 'pos', 'gam', 'wts']}
    f00 = literal_list((ROOT / 'Sqpack/S11Opt/F00/Final.lean').read_text(), 'supp')

    def applies(n, row):
        if n == 0:
            return set(f00) <= set(row)
        d = fields[n]
        return (set(d['supp']) <= set(row) and
                sum(d['gam'][k] for k in d['pos'] if k in row) > sum(d['wts']))

    covered = {n: {i for i, row in enumerate(cases)
                   if applies(n, row) or applies(n, [15 - j for j in row])} for n in [0, 3, 6, 19]}
    inventory = (ROOT / 'ElevenSquare/Tasks/T01/Handoff/Inventory.lean').read_text()
    completed = set()
    for n in [3, 4, 7]:
        pattern = rf'def group{n:03d}Chunk\d+ : List ℕ := (\[[^\n]*\])'
        for text in re.findall(pattern, inventory):
            completed.update(ast.literal_eval(text))
    union = set.union(*covered.values())
    require(union <= set(families['baseline']), 'Imported field covers a non-baseline case')
    report = {
        'status': 'SOURCE_COMPARISON_PASS',
        'canonical_masks_match_in_order': len(cases),
        'families': {name: len(rows) for name, rows in families.items()},
        'generic_cases': len(generic),
        'fields': {str(n): {'count': len(v), 'new_relative_to_G003_G004_G007': len(v - completed)}
                   for n, v in covered.items()},
        'union_count': len(union),
        'existing_completed_union_count': len(completed),
        'new_case_count': len(union - completed),
        'combined_completed_union_count_if_bridge_checked': len(union | completed),
        'remaining_baseline_if_bridge_checked': len(set(families['baseline']) - union - completed),
        'new_cases': sorted(union - completed),
        'covered_cases': sorted(union),
        'kernel_proof': False,
    }
    return report


if __name__ == '__main__':
    print(json.dumps(check(), indent=2))
