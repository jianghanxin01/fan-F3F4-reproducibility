"""Regenerate explicit matching witnesses for the 34-case counting lemma."""
import argparse
import itertools
import json
from pathlib import Path

def pc(x):
    return bin(x).count('1')

def require(condition, message):
    if not condition:
        raise ValueError(message)

def complement(g):
    full = (1 << len(g)) - 1
    return tuple(full ^ (1 << v) ^ row for v, row in enumerate(g))

def matching_certificate(graph, vertices, required):
    """Find explicit disjoint edges by backtracking, independently of the DP."""
    vertices = tuple(vertices)
    if required == 0:
        return []
    if len(vertices) < 2 * required:
        return None
    u = vertices[0]
    rest = vertices[1:]
    for v in rest:
        if graph[u] >> v & 1:
            found = matching_certificate(graph, [w for w in rest if w != v], required - 1)
            if found is not None:
                return [[u, v]] + found
    return matching_certificate(graph, rest, required)

def checked_matching(graph, vertices, required):
    result = matching_certificate(graph, vertices, required)
    require(result is not None, ('Missing matching premise', vertices, required))
    endpoints = [v for edge in result for v in edge]
    require(len(endpoints) == len(set(endpoints)) == 2 * required, 'Matching endpoints repeat')
    require(set(endpoints) <= set(vertices), 'Matching endpoint outside the specified set')
    require(all(graph[u] >> v & 1 for u, v in result), 'Matching uses a nonedge')
    return result

def certify_34(cases):
    """Check only the explicit premises of the short cross-edge-count lemma."""
    left_seeds, right_seeds, conclusions = {}, {}, []
    for case in cases:
        if case['left_index'] not in (80, 280):
            continue
        a, b = tuple(case['left_red']), tuple(case['right_red'])
        require(len(a) == 8 and len(b) == 9, 'Wrong seed orders')
        for graph in (a, b):
            require(all(type(row) is int and not row >> v & 1 and 0 <= row < (1 << len(graph))
                        for v, row in enumerate(graph)), 'Invalid adjacency mask or loop')
            require(all(bool(graph[u] >> v & 1) == bool(graph[v] >> u & 1)
                        for u, v in itertools.combinations(range(len(graph)), 2)), 'Asymmetric adjacency')
        if case['left_index'] in left_seeds:
            require(tuple(left_seeds[case['left_index']]['red']) == a, 'Inconsistent left seed identity')
        if case['right_index'] in right_seeds:
            require(tuple(right_seeds[case['right_index']]['red']) == b, 'Inconsistent right seed identity')
        if case['left_index'] not in left_seeds:
            degrees = [pc(x) for x in a]
            high = [i for i, degree in enumerate(degrees) if degree == 5]
            low = [i for i in range(8) if i not in high]
            require(len(high) == 2 and len(low) == 6, 'Wrong high/low partition')
            require(all(degrees[i] <= 2 for i in low), 'Unexpected low-vertex degree')
            require(not any(all(a[u] >> v & 1 for u, v in itertools.combinations(triple, 2))
                            for triple in itertools.combinations(range(8), 3)), 'Red triangle in left seed')
            blue = complement(a)
            four_sets = []
            for pair in itertools.combinations(low, 2):
                vertices = sorted(high + list(pair))
                four_sets.append({'vertices': vertices, 'blue_matching': checked_matching(blue, vertices, 2)})
            left_seeds[case['left_index']] = {'red': a, 'high': high, 'low': low,
                'red_triangle_free': True, 'four_vertex_blue_matchings': four_sets}
        if case['right_index'] not in right_seeds:
            blue = complement(b)
            degrees = [pc(x) for x in b]
            seven_sets = []
            for vertices in itertools.combinations(range(9), 7):
                seven_sets.append({'vertices': vertices, 'red_matching': checked_matching(b, vertices, 3)})
            roots, leaf_checks = [], []
            for v, degree in enumerate(degrees):
                require(degree >= 1, 'Isolated right-seed vertex is outside lemma')
                vertices = [u for u in range(9) if blue[v] >> u & 1]
                required = 3 if degree <= 2 else 2
                roots.append({'vertex': v, 'internal_red_degree': degree,
                              'blue_matching': checked_matching(blue, vertices, required)})
                if degree == 1:
                    for u in vertices:
                        chosen = [w for w in vertices if w != u]
                        leaf_checks.append({'leaf': v, 'deleted_blue_neighbor': u,
                                            'blue_matching': checked_matching(blue, chosen, 3)})
            right_seeds[case['right_index']] = {'red': b, 'seven_vertex_red_matchings': seven_sets,
                'blue_neighborhood_matchings': roots, 'leaf_deletion_matchings': leaf_checks}
        lower = [8 if pc(row) == 1 else 6 if pc(row) == 2 else 5 for row in b]
        upper = [5 if pc(row) == 5 else 6 for row in a]
        require(sum(upper) == 46 and sum(lower) > 46, 'No strict cross-edge contradiction')
        conclusions.append({'case_id': case['case_id'], 'left_index': case['left_index'],
            'right_index': case['right_index'], 'row_upper_bounds': upper,
            'column_lower_bounds': lower, 'cross_edges_at_most': sum(upper),
            'cross_edges_at_least': sum(lower)})
    require(len(conclusions) == 34 and len({c['case_id'] for c in conclusions}) == 34,
            'Expected exactly34 distinct cases')
    return {'method': 'Explicit matching witnesses and short maximum-cut counting lemma',
            'hypotheses': ['No red F3 or blue F4', 'Every total red degree at most10',
                           'The given8+9 partition satisfies every red-cut swap inequality'],
            'left_seed_certificates': left_seeds, 'right_seed_certificates': right_seeds,
            'conclusions': conclusions, 'excluded_cases': len(conclusions),
            'scope': 'These34 maximum-cut seed pairs only; no global Ramsey claim'}

if __name__ == '__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cases',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    report=certify_34(json.loads(args.cases.read_text(encoding='utf-8')))
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    print('Generated explicit matching certificates for 34 seed pairs.')
