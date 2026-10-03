"""Independent, standard-library checks for the order-17 8+9 gluing search.

This module does not import the production generator, solver, or SAT library.
It verifies graph witnesses exactly.  Catalog profile and row-count audits are
explicitly sampled unless stated otherwise; they are not an UNSAT certificate.
"""
import argparse
import bisect
import functools
import hashlib
import itertools
import json
from pathlib import Path
import random
import sys
import time

TYPES = [(r, t, u) for r in range(9)
         for t in range(min(2, r // 2) + 1)
         for u in range(min(3, (8 - r) // 2) + 1)]
assert len(TYPES) == 49
TYPE_INDEX = {value: i for i, value in enumerate(TYPES)}


def popcount(value):
    # Python 3.6-compatible for cluster nodes without recent Python runtimes.
    return bin(value).count('1')


def require(condition, message):
    if not condition:
        raise ValueError(message)


def validate_graph(red, expected_order=None):
    require(isinstance(red, (list, tuple)), 'Adjacency must be a list')
    n = len(red)
    require(1 <= n <= 17, 'Supported graph order is 1 through 17')
    if expected_order is not None:
        require(n == expected_order, f'Expected order {expected_order}, got {n}')
    full = (1 << n) - 1
    for v, row in enumerate(red):
        require(type(row) is int and 0 <= row <= full,
                f'Invalid integer adjacency mask at vertex {v}')
        require(not row & (1 << v), f'Loop at vertex {v}')
        for w in range(v):
            require(bool(row & (1 << w)) == bool(red[w] & (1 << v)),
                    f'Asymmetric edge {w},{v}')
    return tuple(red)


def complement(red):
    full = (1 << len(red)) - 1
    return tuple(full ^ (1 << v) ^ row for v, row in enumerate(red))


def matching_oracle(red):
    """Maximum matching DP, shared over all requested induced vertex sets."""
    @functools.lru_cache(None)
    def maximum(mask):
        if not mask:
            return 0
        bit = mask & -mask
        v = bit.bit_length() - 1
        rest = mask ^ bit
        answer = maximum(rest)
        choices = red[v] & rest
        while choices:
            mate = choices & -choices
            choices ^= mate
            answer = max(answer, 1 + maximum(rest ^ mate))
        return answer

    def witness(mask):
        result = []
        while mask:
            target = maximum(mask)
            if target == 0:
                break
            bit = mask & -mask
            v = bit.bit_length() - 1
            rest = mask ^ bit
            if maximum(rest) == target:
                mask = rest
                continue
            choices = red[v] & rest
            while choices:
                mate = choices & -choices
                choices ^= mate
                if 1 + maximum(rest ^ mate) == target:
                    result.append([v, mate.bit_length() - 1])
                    mask = rest ^ mate
                    break
            else:
                raise AssertionError('Matching reconstruction failed')
        return result
    return maximum, witness


def contains_clique(adj, size):
    if len(adj) < size:
        return False
    for vertices in itertools.combinations(range(len(adj)), size):
        if all(adj[v] & (1 << w) for v, w in itertools.combinations(vertices, 2)):
            return True
    return False


def fan_report(red):
    red = validate_graph(red)
    report = {'order': len(red), 'valid': True, 'forbidden_fans': [],
              'red_degrees': [popcount(row) for row in red],
              'red_edges': sum(popcount(row) for row in red) // 2,
              'method': 'independent maximum-matching subset DP'}
    for colour, adj, threshold in [('red', red, 3), ('blue', complement(red), 4)]:
        maximum, witness = matching_oracle(adj)
        numbers = [maximum(adj[v]) for v in range(len(adj))]
        report[colour + '_neighborhood_matching_numbers'] = numbers
        for v, number in enumerate(numbers):
            if number >= threshold:
                report['valid'] = False
                report['forbidden_fans'].append({
                    'colour': colour, 'centre': v,
                    'matching': witness(adj[v])[:threshold]})
    return report


def seed_ok(red):
    if not fan_report(red)['valid']:
        return False
    return not contains_clique(red, 6) and not contains_clique(complement(red), 8)


def graph6_decode(line, expected_order=None):
    if isinstance(line, bytes):
        line = line.decode('ascii')
    require(bool(line) and all(63 <= ord(c) <= 126 for c in line),
            'Invalid graph6 characters')
    n = ord(line[0]) - 63
    require(n in (8, 9), 'Expected compact graph6 order 8 or 9')
    require(len(line) == 1 + (n * (n - 1) // 2 + 5) // 6,
            'Wrong graph6 record length')
    if expected_order is not None:
        require(n == expected_order, 'Wrong graph6 order')
    red = [0] * n
    at = 0
    for v in range(1, n):
        for u in range(v):
            if (ord(line[1 + at // 6]) - 63) & (1 << (5 - at % 6)):
                red[u] |= 1 << v
                red[v] |= 1 << u
            at += 1
    # Compact graph6 unused tail bits must be zero.
    while at % 6:
        require(not ((ord(line[1 + at // 6]) - 63) & (1 << (5 - at % 6))),
                'Nonzero graph6 padding')
        at += 1
    return validate_graph(red, expected_order)


def append_vertex(red, mask):
    n = len(red)
    return tuple(row | ((1 << n) if mask & (1 << v) else 0)
                 for v, row in enumerate(red)) + (mask,)


def legal_extensions_direct(red):
    """Oracle: form each full child and scan all centres and clique subsets."""
    require(seed_ok(red), 'Input is not a legal seed')
    return [mask for mask in range(1 << len(red))
            if seed_ok(append_vertex(red, mask))]


def legal_extensions_conflicts(red):
    """The mathematical conflict criterion, checked against the direct oracle."""
    n = len(red)
    full = (1 << n) - 1
    blue = complement(red)
    mr, _ = matching_oracle(red)
    mb, _ = matching_oracle(blue)
    conflicts = []
    for adj, match, cap in [(red, mr, 2), (blue, mb, 3)]:
        conflicts.append({(1 << u) | (1 << v)
                          for u in range(n) for v in range(n)
                          if adj[u] & (1 << v)
                          and match(adj[u] & ~(1 << v)) >= cap})
    red_cliques = [sum(1 << v for v in vv)
                   for vv in itertools.combinations(range(n), 5)
                   if all(red[u] & (1 << v)
                          for u, v in itertools.combinations(vv, 2))]
    blue_cliques = [sum(1 << v for v in vv)
                    for vv in itertools.combinations(range(n), 7)
                    if all(blue[u] & (1 << v)
                           for u, v in itertools.combinations(vv, 2))]
    result = []
    for mask in range(1 << n):
        other = full ^ mask
        if mr(mask) > 2 or mb(other) > 3:
            continue
        if any(mask & p == p for p in conflicts[0] | set(red_cliques)):
            continue
        if any(other & p == p for p in conflicts[1] | set(blue_cliques)):
            continue
        result.append(mask)
    return result


def independent_profile(red, opposite_order, direct=True):
    require(len(red) + opposite_order == 17, 'Profile order mismatch')
    require(seed_ok(red), 'Invalid profile seed')
    n = len(red)
    full = (1 << n) - 1
    blue = complement(red)
    mr, _ = matching_oracle(red)
    mb, _ = matching_oracle(blue)
    patterns = legal_extensions_direct(red) if direct else legal_extensions_conflicts(red)
    degrees = [popcount(r) for r in red]
    maximum = max(degrees)
    high = sum(1 << v for v, d in enumerate(degrees) if d == maximum)
    support = 0
    for v, d in enumerate(degrees):
        support |= 1 << TYPE_INDEX[d, mr(red[v]), mb(blue[v])]
    allowed = 0
    for i, (r, t, u) in enumerate(TYPES):
        if any(7 <= r + popcount(mask) <= 10
               and t + mr(mask) <= 2 and u + mb(full ^ mask) <= 3
               for mask in patterns):
            allowed |= 1 << i
    flags = 0
    for k in range(3):
        if any(popcount(mask) == maximum and not mask & high
               and mr(mask) <= k for mask in patterns):
            flags |= 1 << k
    max_root_nu = max(mr(red[v]) for v, d in enumerate(degrees) if d == maximum)
    edge_count = sum(degrees) // 2
    return [maximum, edge_count, 7 * n - 2 * edge_count,
            sum(min(opposite_order, 10 - d) for d in degrees),
            support, allowed, max_root_nu, flags]


def compatible(a, b):
    if a[0] + b[0] > 10 or max(0, a[2], b[2]) > min(72, a[3], b[3]):
        return False
    if a[4] & ~b[5] or b[4] & ~a[5]:
        return False
    if a[0] + b[0] == 10:
        if not (b[7] & (1 << (2 - a[6])) and a[7] & (1 << (2 - b[6]))):
            return False
    return True


def graph_from_edges(n, edges):
    red = [0] * n
    for u, v in edges:
        red[u] |= 1 << v
        red[v] |= 1 << u
    return tuple(red)


def independent_matching_brute(red, vertices, need):
    """Small-fixture oracle: enumerate edge combinations, not vertex DP."""
    edges = [(1 << u) | (1 << v)
             for u, v in itertools.combinations(vertices, 2)
             if red[u] & (1 << v)]
    for chosen in itertools.combinations(edges, need):
        union = 0
        for edge in chosen:
            union |= edge
        if popcount(union) == 2 * need:
            return True
    return need == 0


def glue(left, right, cross):
    m, n = len(left), len(right)
    require(len(cross) == m * n and all(type(x) is int and x in (0, 1) for x in cross),
            'Invalid cross matrix')
    red = list(left) + [row << m for row in right]
    for i in range(m):
        for j in range(n):
            if cross[n * i + j]:
                red[i] |= 1 << (m + j)
                red[m + j] |= 1 << i
    return validate_graph(red, m + n)


def cross_count(red, a, b):
    return sum(bool(red[u] & (1 << v)) for u in a for v in b)


def self_test():
    rng = random.Random(170809)
    extension_cases = 0
    fixture_profiles = []
    for n in (8, 9):
        fixtures = [
            ('cycle', graph_from_edges(n, [(v, (v + 1) % n) for v in range(n)])),
            ('path', graph_from_edges(n, [(v, v + 1) for v in range(n - 1)])),
            ('bipartite', graph_from_edges(n, [(u, v) for u in range(n // 2)
                                              for v in range(n // 2, n)])),
            ('bipartite3', graph_from_edges(n, [(u, v) for u in range(3)
                                               for v in range(3, n)])),
            ('clique5', graph_from_edges(n, itertools.combinations(range(5), 2)))]
        for name, red in fixtures:
            direct = legal_extensions_direct(red)
            require(direct == legal_extensions_conflicts(red),
                    f'Extension criteria disagree on {n}-{name}')
            extension_cases += 1 << n
            p = independent_profile(red, 17 - n)
            fixture_profiles.append({'name': f'{name}{n}', 'red_adjacency': list(red),
                                     'profile': p, 'legal_extension_count': len(direct)})
            for colour, adj in [('red', red), ('blue', complement(red))]:
                maximum, _ = matching_oracle(adj)
                for _ in range(12):
                    vertices = sorted(rng.sample(range(n), rng.randrange(1, n + 1)))
                    mask = sum(1 << v for v in vertices)
                    for need in range(min(3, len(vertices) // 2) + 1):
                        require((maximum(mask) >= need) == independent_matching_brute(adj, vertices, need),
                                f'Matching DP disagrees with edge oracle for {colour}')
        require(not seed_ok(tuple(0 for _ in range(n))), 'Blue clique passed seed test')
        require(not seed_ok(complement(tuple(0 for _ in range(n)))),
                'Red clique passed seed test')

    # Every valid target seed has a valid one-vertex-deleted induced seed.
    closure_checks = 0
    for rec in fixture_profiles:
        red = tuple(rec['red_adjacency'])
        for removed in range(len(red)):
            vertices = [v for v in range(len(red)) if v != removed]
            child = tuple(sum(1 << j for j, w in enumerate(vertices) if red[v] & (1 << w))
                          for v in vertices)
            require(seed_ok(child), 'Hereditary seed restriction failed')
            closure_checks += 1

    require({9 * i + j for i in range(8) for j in range(9)} == set(range(72)),
            '8x9 indexing is not bijective')
    swap_checks = 0
    for _ in range(10):
        red = graph_from_edges(17, [(u, v) for u in range(17) for v in range(u + 1, 17)
                                    if rng.random() < .43])
        a, b = set(range(8)), set(range(8, 17))
        before = cross_count(red, a, b)
        for u in a:
            for v in b:
                ra = sum(bool(red[u] & (1 << w)) for w in a)
                rb = sum(bool(red[v] & (1 << w)) for w in b)
                cu = sum(bool(red[u] & (1 << w)) for w in b)
                cv = sum(bool(red[v] & (1 << w)) for w in a)
                delta = ra + rb - cu - cv + 2 * bool(red[u] & (1 << v))
                after = cross_count(red, (a - {u}) | {v}, (b - {v}) | {u})
                require(after - before == delta, 'Cross-swap identity failed')
                swap_checks += 1
        while True:
            improvement = None
            for u in sorted(a):
                for v in sorted(b):
                    new_a, new_b = (a - {u}) | {v}, (b - {v}) | {u}
                    value = cross_count(red, new_a, new_b)
                    if value > before:
                        improvement = new_a, new_b, value
                        break
                if improvement:
                    break
            if improvement is None:
                break
            a, b, before = improvement
        for u in a:
            for v in b:
                ra = sum(bool(red[u] & (1 << w)) for w in a)
                rb = sum(bool(red[v] & (1 << w)) for w in b)
                require(2 * (ra + rb + bool(red[u] & (1 << v))) <=
                        popcount(red[u]) + popcount(red[v]),
                        'Local maximum cut inequality failed')

    k88 = graph_from_edges(16, [(u, v) for u in range(8) for v in range(8, 16)])
    require(fan_report(k88)['valid'], 'Known order16 witness rejected')
    require(not fan_report(append_vertex(k88, 0))['valid'], 'Invalid extension accepted')
    left = graph_from_edges(8, [(v, (v + 1) % 8) for v in range(8)])
    right = graph_from_edges(9, [(v, (v + 1) % 9) for v in range(9)])
    for position in range(72):
        bits = [0] * 72
        bits[position] = 1
        red = glue(left, right, bits)
        i, j = divmod(position, 9)
        require(red[i] & (1 << (8 + j)) and red[8 + j] & (1 << i),
                'Cross edge has wrong global endpoints')
        require(sum(popcount(row) for row in red) // 2 == 18,
                'Cross edge count was not preserved')
    # Ordered, unequal-size roles never use triangular/diagonal counting.
    groups_l, groups_r = [[2, 4], [8]], [[1, 3, 5], [7, 9]]
    flattened = [(x, y) for aa in groups_l for bb in groups_r for x in aa for y in bb]
    require(len(flattened) == 15 and len(set(flattened)) == 15,
            'Ordered Cartesian indexing fixture failed')
    for aa in groups_l:
        for bb in groups_r:
            for position, pair in enumerate(itertools.product(aa, bb)):
                q, r = divmod(position, len(bb))
                require(pair == (aa[q], bb[r]), 'Cartesian block indexing failed')
    # Isolate the direction of the saturated-boundary bit test.  These are
    # predicate fixtures, not asserted realizable complete seed profiles.
    pa = [4, 0, 0, 72, 1, 1, 2, 4]
    pb = [6, 0, 0, 72, 1, 1, 0, 7]
    require(compatible(pa, pb) and compatible(pb, pa), 'Boundary flag direction failed')
    pb[7] = 4
    require(not compatible(pa, pb), 'Opposite root residual zero was ignored')
    pa[0] = 3
    require(compatible(pa, pb), 'Boundary flag incorrectly used below degree sum ten')
    # Masks must remain integer, loop-free, symmetric, and within their order.
    for malformed in ([True], [1], [2], [0, 1], [0.0]):
        try:
            validate_graph(malformed)
        except ValueError:
            pass
        else:
            raise AssertionError('Malformed graph was accepted')
    return {'self_test': 'passed', 'direct_extension_checks': extension_cases,
            'seed_closure_checks': closure_checks, 'cross_swap_checks': swap_checks,
            'cross_index_checks': 72, 'profile_fixtures': fixture_profiles,
            'scope': 'Independent small-fixture checks; no exhaustive17 search or UNSAT claim'}


def read_witness(path, order):
    raw = json.loads(Path(path).read_text(encoding='utf-8'))
    if isinstance(raw, dict) and 'witness' in raw and isinstance(raw['witness'], dict):
        raw = raw['witness']
    if isinstance(raw, dict) and 'red_adjacency' in raw:
        red = raw['red_adjacency']
    elif isinstance(raw, list):
        red = raw
    elif isinstance(raw, dict) and 'red_edges' in raw:
        n = raw.get('n', raw.get('order', order))
        require(type(n) is int and n == order, 'Wrong witness order')
        red = [0] * n
        seen = set()
        for edge in raw['red_edges']:
            require(isinstance(edge, list) and len(edge) == 2, 'Invalid edge record')
            u, v = edge
            require(type(u) is int and type(v) is int and 0 <= u < n and 0 <= v < n and u != v,
                    'Invalid edge endpoints')
            key = tuple(sorted((u, v)))
            require(key not in seen, 'Repeated edge')
            seen.add(key)
            red[u] |= 1 << v
            red[v] |= 1 << u
    else:
        raise ValueError('Expected red_adjacency, a bare adjacency list, or red_edges')
    return validate_graph(red, order)


def check_catalog(directory, profile_samples=4, case_samples=12):
    directory = Path(directory)
    cat_path = directory / 'catalog.json'
    catalog = json.loads(cat_path.read_text(encoding='utf-8'))
    require(catalog['format'] == 'fan17-catalog-1', 'Wrong catalog format')
    require(catalog['orders'] == [8, 9], 'Wrong ordered block dimensions')
    require(catalog['seed_counts'] == [8812, 115174], 'Unexpected seed counts')
    require(catalog['center_types'] == [list(value) for value in TYPES],
            'Center-type bit order differs from the independently defined 49 types')
    profiles = [catalog['profiles_left'], catalog['profiles_right']]
    graphs = []
    hashes = {'catalog.json': hashlib.sha256(cat_path.read_bytes()).hexdigest()}
    for side, (n, name) in enumerate([(8, 'fan8_target17.graph6'), (9, 'fan9_target17.graph6')]):
        path = directory / name
        raw = path.read_bytes()
        hashes[name] = hashlib.sha256(raw).hexdigest()
        lines = raw.splitlines()
        require(len(lines) == catalog['seed_counts'][side], 'Incomplete seed file')
        graphs.append([graph6_decode(line, n) for line in lines])
    rng = random.Random(1789001)
    sampled_profiles = []
    for side, n in enumerate((8, 9)):
        seen = set()
        first_ids = []
        mapping = {}
        for group_index, entry in enumerate(profiles[side]):
            p, ids = entry['p'], entry['ids']
            require(len(p) == 8 and all(type(x) is int for x in p), 'Invalid profile shape')
            require(0 <= p[4] < (1 << 49) and 0 <= p[5] < (1 << 49)
                    and 0 <= p[6] <= 2 and 0 <= p[7] <= 7, 'Invalid type/flag field')
            require(ids and ids == sorted(ids), 'Unordered or empty seed group')
            first_ids.append(ids[0])
            for seed in ids:
                require(type(seed) is int and 0 <= seed < len(graphs[side]) and seed not in seen,
                        'Duplicate or invalid seed index')
                seen.add(seed)
                mapping[seed] = group_index
                degree = [popcount(row) for row in graphs[side][seed]]
                edge_count = sum(degree) // 2
                basic = [max(degree), edge_count, 7 * n - 2 * edge_count,
                         sum(min(17 - n, 10 - d) for d in degree)]
                require(p[:4] == basic, f'Basic profile mismatch side{side} seed{seed}')
        require(len(seen) == len(graphs[side]), 'Seed index partition incomplete')
        require(first_ids == sorted(first_ids), 'Groups are not in first-occurrence order')
        require(len(profiles[side]) == catalog['profile_counts'][side], 'Wrong profile count')
        indices = {0, len(graphs[side]) - 1}
        while len(indices) < min(profile_samples, len(graphs[side])):
            indices.add(rng.randrange(len(graphs[side])))
        for seed in sorted(indices):
            red = graphs[side][seed]
            calculated = independent_profile(red, 17 - n, direct=True)
            expected = profiles[side][mapping[seed]]['p']
            require(calculated == expected, f'Full profile mismatch side{side} seed{seed}')
            require(legal_extensions_direct(red) == legal_extensions_conflicts(red),
                    f'Extension check mismatch side{side} seed{seed}')
            sampled_profiles.append({'side': side, 'seed': seed, 'profile': calculated})
    prefix = [0]
    for entry in profiles[0]:
        count = entry['pairs']
        require(type(count) is int and count >= 0, 'Invalid profile row count')
        prefix.append(prefix[-1] + count)
    require(prefix[-1] == catalog['total_pairs'] and prefix[-1] > 0,
            'Catalog total differs from row sum')
    total = prefix[-1]
    rows = {}

    def row_blocks(i):
        if i not in rows:
            blocks = []
            local_prefix = [0]
            for j, right in enumerate(profiles[1]):
                if compatible(profiles[0][i]['p'], right['p']):
                    blocks.append(j)
                    local_prefix.append(local_prefix[-1] +
                                        len(profiles[0][i]['ids']) * len(right['ids']))
            require(local_prefix[-1] == profiles[0][i]['pairs'],
                    f'Sampled row {i} pair-count mismatch')
            rows[i] = blocks, local_prefix
        return rows[i]

    cases = {0, total - 1}
    while len(cases) < min(case_samples, total):
        cases.add(rng.randrange(total))
    fixtures = []
    for case in sorted(cases):
        i = bisect.bisect_right(prefix, case) - 1
        blocks, local_prefix = row_blocks(i)
        local = case - prefix[i]
        block = bisect.bisect_right(local_prefix, local) - 1
        j = blocks[block]
        left_ids, right_ids = profiles[0][i]['ids'], profiles[1][j]['ids']
        offset = local - local_prefix[block]
        m, n = divmod(offset, len(right_ids))
        require(0 <= m < len(left_ids) and 0 <= n < len(right_ids), 'Pair offset outside block')
        require(prefix[i] + local_prefix[block] + m * len(right_ids) + n == case,
                'Case-index round trip failed')
        fixtures.append({'case': case, 'seed_indices': [left_ids[m], right_ids[n]]})
    return {'catalog_validation': 'passed', 'orders': [8, 9],
            'all_seed_basic_profiles_checked': [len(g) for g in graphs],
            'sampled_full_profiles': sampled_profiles, 'sampled_rows': sorted(rows),
            'index_cases': fixtures, 'total_pairs': total, 'sha256': hashes,
            'scope': 'All seed records/basic fields and sampled full profiles/rows; no UNSAT proof'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='command')
    test = sub.add_parser('self-test')
    test.add_argument('--output', type=Path)
    data = sub.add_parser('data')
    data.add_argument('--data', type=Path, default=Path(__file__).resolve().parent.parent/'data')
    data.add_argument('--profile-samples', type=int, default=4)
    data.add_argument('--case-samples', type=int, default=12)
    data.add_argument('--output', type=Path)
    data.add_argument('--case-fixtures', type=Path,
                      help='Write a case/seed-index array accepted by the C++ pilot')
    verify = sub.add_parser('verify')
    verify.add_argument('--input', '--witness', dest='input', type=Path, required=True)
    verify.add_argument('--order', type=int, default=17)
    verify.add_argument('--output', type=Path)
    argv = sys.argv[1:]
    # A copied standalone verify17.py supports the short cluster-facing form:
    # python3 verify17.py --witness results/witness.json
    if '--witness' in argv and (not argv or argv[0] not in ('self-test', 'data', 'verify')):
        argv = ['verify'] + argv
    args = parser.parse_args(argv)
    if args.command is None:
        parser.error('Choose self-test, data, or verify; or supply --witness PATH')
    began = time.monotonic()
    try:
        if args.command == 'self-test':
            result = self_test()
        elif args.command == 'data':
            require(args.profile_samples >= 2 and args.case_samples >= 2,
                    'At least two profiles/cases are required')
            result = check_catalog(args.data, args.profile_samples, args.case_samples)
            if args.case_fixtures:
                args.case_fixtures.parent.mkdir(parents=True, exist_ok=True)
                args.case_fixtures.write_text(json.dumps(result['index_cases'], indent=2) + '\n',
                                             encoding='utf-8')
        else:
            result = fan_report(read_witness(args.input, args.order))
        result['elapsed_seconds'] = round(time.monotonic() - began, 6)
        if args.output:
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
        print(json.dumps(result, indent=2))
        return 0 if result.get('valid', True) else 1
    except (ValueError, KeyError, TypeError, IndexError, OSError, json.JSONDecodeError) as error:
        print(json.dumps({'error': str(error), 'elapsed_seconds':
                          round(time.monotonic() - began, 6)}))
        return 2


if __name__ == '__main__':
    raise SystemExit(main())
