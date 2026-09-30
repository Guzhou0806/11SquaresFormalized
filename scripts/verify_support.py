"""Pure scheduling, receipt, and axiom checks used by the serial verifier."""
import hashlib
import heapq
import json
import re


def priority_order(dependencies, sizes, final='ElevenSquare.Verification'):
    """Check shared interfaces before independent certificate leaves, serially."""
    users = {m: set() for m in dependencies}
    remaining = {m: len(set(ds)) for m, ds in dependencies.items()}
    for m, ds in dependencies.items():
        for dep in ds:
            users[dep].add(m)
    if users.get(final):
        raise ValueError('The final audit module must not have local dependents')
    key = lambda m: (m == final, -len(users[m]), sizes[m], m)
    ready = [key(m) for m, n in remaining.items() if n == 0]
    heapq.heapify(ready)
    order = []
    while ready:
        m = heapq.heappop(ready)[-1]
        order.append(m)
        for user in users[m]:
            remaining[user] -= 1
            if remaining[user] == 0:
                heapq.heappush(ready, key(user))
    if len(order) != len(dependencies):
        raise ValueError('Local import cycle')
    return order


def input_digest(inputs):
    return hashlib.sha256(json.dumps(inputs, sort_keys=True).encode()).hexdigest()


def reusable_inputs(old, current, *, legacy_baseline, checked_at, newest_input):
    if old == current:
        return True
    # Old receipts recorded only direct object hashes. Migrate them only in the
    # original checkout: its logs, objects and all dependency checks must predate
    # the receipt. Future receipts use hashes, including transitive input hashes.
    legacy = {k: v for k, v in current.items()
              if k not in {'build_context', 'local_dependency_inputs'}}
    return (legacy_baseline and old == legacy and newest_input <= checked_at)


def audit_axioms(source_code, output, allowed, unfinished):
    queries = re.findall(r'^\s*#print\s+axioms\s+(\S+)', source_code, re.M)
    printed = re.findall(
        r"^'([^']+)' (?:depends on axioms: \[([^]]*)\]|(does not depend on any axioms))",
        output, re.M)
    if len(queries) != len(printed):
        raise ValueError(f'Expected {len(queries)} axiom outputs, found {len(printed)}')
    seen = {}
    for query, (name, axioms, _) in zip(queries, printed):
        query = query.removeprefix('_root_.')
        if name != query and not name.endswith('.' + query):
            raise ValueError('Missing axiom output: ' + query)
        axioms = {a.strip() for a in axioms.split(',') if a.strip()}
        extra = axioms - allowed - ({'sorryAx'} if name in unfinished else set())
        if extra:
            raise ValueError('Unapproved axioms in ' + name + ': ' + str(sorted(extra)))
        seen[name] = sorted(axioms)
    return seen
