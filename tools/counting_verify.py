"""Check the explicit witnesses for the 34-case counting lemma.

Every matching edge is inspected directly. No matching search, SAT solver,
canonical-labeling library, or third-party Python package is used.
"""
import itertools


def require(test, message):
    if not test:
        raise ValueError(message)


def pc(mask):
    return bin(mask).count('1')


def complement(g):
    return [(1 << len(g)) - 1 ^ (1 << v) ^ row for v, row in enumerate(g)]


def check_matching(graph, allowed, edges, size):
    require(isinstance(edges, list) and len(edges) == size, 'Wrong matching length')
    endpoints = []
    for edge in edges:
        require(isinstance(edge, list) and len(edge) == 2, 'Matching edge format')
        u, v = edge
        require(type(u) is int and type(v) is int and u in allowed and v in allowed and u != v,
                'Matching endpoint outside the prescribed vertices')
        require(graph[u] >> v & 1 and graph[v] >> u & 1, 'Matching nonedge')
        endpoints.extend(edge)
    require(len(set(endpoints)) == 2 * size, 'Matching endpoints overlap')


def verify(cert, cases):
    selected = [c for c in cases if c['left_index'] in (80, 280)]
    require(len(selected) == 34 and len({c['case_id'] for c in selected}) == 34, 'Wrong 34-case set')
    left = {c['left_index']: c['left_red'] for c in selected}
    right = {c['right_index']: c['right_red'] for c in selected}
    require(set(cert['left_seed_certificates']) == {str(k) for k in left}, 'Left certificate coverage')
    require(set(cert['right_seed_certificates']) == {str(k) for k in right}, 'Right certificate coverage')
    witnesses = 0
    for index, a in left.items():
        item = cert['left_seed_certificates'][str(index)]
        require(item['red'] == a, 'Left adjacency mismatch')
        degrees = list(map(pc, a))
        high = [v for v, d in enumerate(degrees) if d == 5]
        low = [v for v, d in enumerate(degrees) if d <= 2]
        require(len(high) == 2 and len(low) == 6 and sorted(high + low) == list(range(8)),
                'Wrong left degree partition')
        require(item['high'] == high and item['low'] == low, 'Left partition differs')
        require(all(not all(a[u] >> v & 1 for u, v in itertools.combinations(triple, 2))
                    for triple in itertools.combinations(range(8), 3)), 'Left red triangle')
        expected = {tuple(sorted(high + list(pair))) for pair in itertools.combinations(low, 2)}
        seen = set()
        for proof in item['four_vertex_blue_matchings']:
            vs = tuple(proof['vertices'])
            require(vs in expected and vs not in seen, 'Repeated or unexpected left four-set')
            check_matching(complement(a), set(vs), proof['blue_matching'], 2)
            seen.add(vs)
            witnesses += 1
        require(seen == expected, 'Missing left four-set witness')
    for index, b in right.items():
        item = cert['right_seed_certificates'][str(index)]
        require(item['red'] == b, 'Right adjacency mismatch')
        blue = complement(b)
        degree = list(map(pc, b))
        require(min(degree) >= 1, 'Isolated right vertex outside the lemma')
        expected = set(itertools.combinations(range(9), 7))
        seen = set()
        for proof in item['seven_vertex_red_matchings']:
            vs = tuple(proof['vertices'])
            require(vs in expected and vs not in seen, 'Repeated or unexpected right seven-set')
            check_matching(b, set(vs), proof['red_matching'], 3)
            seen.add(vs)
            witnesses += 1
        require(seen == expected, 'Missing right seven-set witness')
        seen = set()
        for proof in item['blue_neighborhood_matchings']:
            v = proof['vertex']
            require(type(v) is int and v in range(9) and v not in seen, 'Repeated or invalid right root')
            require(proof['internal_red_degree'] == degree[v], 'Right root degree mismatch')
            allowed = {u for u in range(9) if blue[v] >> u & 1}
            check_matching(blue, allowed, proof['blue_matching'], 3 if degree[v] <= 2 else 2)
            seen.add(v)
            witnesses += 1
        require(seen == set(range(9)), 'Missing right root witness')
        expected = {(v, u) for v in range(9) if degree[v] == 1 for u in range(9) if blue[v] >> u & 1}
        seen = set()
        for proof in item['leaf_deletion_matchings']:
            v, u = proof['leaf'], proof['deleted_blue_neighbor']
            require((v, u) in expected and (v, u) not in seen, 'Repeated or invalid leaf deletion')
            allowed = {w for w in range(9) if w != u and blue[v] >> w & 1}
            check_matching(blue, allowed, proof['blue_matching'], 3)
            seen.add((v, u))
            witnesses += 1
        require(seen == expected, 'Missing leaf-deletion witness')
    conclusions = {r['case_id']: r for r in cert['conclusions']}
    require(len(cert['conclusions']) == len(conclusions) == 34
            and set(conclusions) == {c['case_id'] for c in selected}, 'Conclusion case coverage')
    for case in selected:
        row = conclusions[case['case_id']]
        upper = [5 if pc(mask) == 5 else 6 for mask in case['left_red']]
        lower = [8 if pc(mask) == 1 else 6 if pc(mask) == 2 else 5 for mask in case['right_red']]
        require(row['left_index'] == case['left_index'] and row['right_index'] == case['right_index'],
                'Conclusion seed index mismatch')
        require(row['row_upper_bounds'] == upper and row['column_lower_bounds'] == lower,
                'Conclusion degree bounds mismatch')
        require(row['cross_edges_at_most'] == sum(upper) == 46
                and row['cross_edges_at_least'] == sum(lower) > 46, 'No strict counting contradiction')
    return {'status': 'COUNTING_CERTIFICATE_VERIFIED', 'case_ids': sorted(conclusions),
            'cases': 34, 'explicit_matching_witnesses_checked': witnesses,
            'full_search_verified': False}
