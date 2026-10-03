"""Replay finite-domain exclusion certificates without a SAT/matching solver.

Every deleted initial pattern and every used incompatible row pair is justified
by an explicit monochromatic fan (centre and disjoint matching endpoints).
The checker verifies each edge directly from the fixed seeds and known rows.
All domain deletions and every exhaustive search branch are then replayed.

The mathematical premises are red degree in [7,10] and a maximum balanced
red cut of sizes8+9. No isomorphism reduction is used in these certificates.
This checks only the supplied seed-pair exclusions, not the full catalog.
"""
import argparse
import hashlib
import json
from pathlib import Path
import time


def require(test, message):
    if not test:
        raise ValueError(message)


def pc(mask):
    return bin(mask).count('1')


class Checker:
    def __init__(self, cert, expected=None):
        self.cert = cert
        require(cert['schema'] == 'fan17-csp-certificate-1', 'Unknown schema')
        self.a, self.b = cert['left_red'], cert['right_red']
        for adj, n in [(self.a, 8), (self.b, 9)]:
            require(len(adj) == n, 'Seed order')
            for v, mask in enumerate(adj):
                require(type(mask) is int and 0 <= mask < 1 << n, 'Adjacency range')
                require(not (mask >> v & 1), 'Loop')
                for w in range(n):
                    require((mask >> w & 1) == (adj[w] >> v & 1), 'Asymmetric adjacency')
        if expected is not None:
            require(cert['case_id'] == expected['case_id'], 'Case identity mismatch')
            require(self.a == expected['left_red'] and self.b == expected['right_red'],
                    'Seed adjacency differs from received case')
        self.da, self.db = list(map(pc, self.a)), list(map(pc, self.b))
        self.fans = self.nodes = self.deletions = self.leaves = 0
        self.pairs = set()

    def edge(self, u, v, rows, cols):
        require(u != v and 0 <= u < 17 and 0 <= v < 17, 'Bad edge endpoints')
        if u < 8 and v < 8:
            return 0 if self.a[u] >> v & 1 else 1
        if u >= 8 and v >= 8:
            return 0 if self.b[u-8] >> (v-8) & 1 else 1
        if u >= 8:
            u, v = v, u
        j = v - 8
        value = (rows[u] >> j & 1) if u in rows else None
        if j in cols:
            new = cols[j] >> u & 1
            require(value is None or value == new, 'Inconsistent row and column')
            value = new
        return None if value is None else (0 if value else 1)

    def fan(self, proof, rows=None, cols=None):
        rows, cols = rows or {}, cols or {}
        require(isinstance(proof, list) and len(proof) == 3, 'Fan proof format')
        color, centre, endpoints = proof
        require(type(color) is int and color in (0, 1), 'Fan colour')
        require(type(centre) is int and 0 <= centre < 17, 'Fan centre')
        require(isinstance(endpoints, list) and len(endpoints) == (6 if color == 0 else 8),
                'Wrong matching length')
        require(all(type(v) is int and 0 <= v < 17 for v in endpoints), 'Endpoint range')
        require(len(set(endpoints)) == len(endpoints) and centre not in endpoints,
                'Matching endpoints not distinct from each other and centre')
        for v in endpoints:
            require(self.edge(centre, v, rows, cols) == color, 'Fan spoke missing/wrong colour')
        for u, v in zip(endpoints[::2], endpoints[1::2]):
            require(self.edge(u, v, rows, cols) == color, 'Matching edge missing/wrong colour')
        self.fans += 1

    @staticmethod
    def pairkey(i, m, k, q):
        if i > k:
            i, m, k, q = k, q, i, m
        require(0 <= i < k < 8 and 0 <= m < 512 and 0 <= q < 512, 'Pair key range')
        return ((i * 512 + m) * 8 + k) * 512 + q

    def compatible_cross(self, i, m, j, q):
        bit = m >> j & 1
        return bit == (q >> i & 1) and pc(m) + pc(q) - 2 * bit >= self.da[i] + self.db[j]

    def initial(self):
        rows = [{m for m in range(512) if 7 <= self.da[i] + pc(m) <= 10} for i in range(8)]
        cols = [{m for m in range(256) if 7 <= self.db[j] + pc(m) <= 10} for j in range(9)]
        for axis, vertex, mask, proof in self.cert['initial_rejections']:
            require(axis in (0, 1), 'Rejection axis')
            ds = rows if axis == 0 else cols
            require(0 <= vertex < len(ds) and mask in ds[vertex], 'Invalid/repeated initial deletion')
            self.fan(proof, {vertex: mask} if axis == 0 else {},
                     {vertex: mask} if axis == 1 else {})
            ds[vertex].remove(mask)
        for domains, named in [(rows, 'initial_rows'), (cols, 'initial_columns')]:
            saved = self.cert[named]
            require(len(saved) == len(domains), 'Initial domain count')
            for got, want in zip(saved, domains):
                require(len(got) == len(set(got)) and set(got) == want,
                        'An initial pattern was omitted without a checked witness')
        for key, proof in self.cert['pair_rejections']:
            require(type(key) is int and 0 <= key < 8*512*8*512 and key not in self.pairs,
                    'Invalid/repeated pair key')
            q, rest = key % 512, key // 512
            k, rest = rest % 8, rest // 8
            m, i = rest % 512, rest // 512
            require(i < k, 'Noncanonical pair key')
            require(m in rows[i] and q in rows[k], 'Pair outside initial domains')
            self.fan(proof, {i: m, k: q})
            self.pairs.add(key)
        return rows, cols

    def node(self, tree, rows, cols):
        self.nodes += 1
        for axis, vertex, mask, reason, target in tree['deletions']:
            require(axis in (0, 1) and reason in (0, 1), 'Deletion code')
            domains = rows if axis == 0 else cols
            require(0 <= vertex < len(domains) and mask in domains[vertex], 'Repeated/absent deletion')
            if axis == 0 and reason == 0:
                require(0 <= target < 8 and target != vertex, 'Pair-support target')
                require(all(self.pairkey(vertex, mask, target, q) in self.pairs for q in rows[target]),
                        'Deleted row has no checked incompatibility with some possible support')
            elif axis == 0 and reason == 1:
                require(0 <= target < 9, 'Column-support target')
                require(all(not self.compatible_cross(vertex, mask, target, q) for q in cols[target]),
                        'Deleted row still has a column support')
            else:
                require(reason == 1 and 0 <= target < 8, 'Row-support target')
                require(all(not self.compatible_cross(target, q, vertex, mask) for q in rows[target]),
                        'Deleted column still has a row support')
            domains[vertex].remove(mask)
            self.deletions += 1
        kind = tree['kind']
        if kind == 'empty':
            require(any(not d for d in rows + cols), 'Empty leaf has no empty domain')
            self.leaves += 1
        elif kind == 'fan':
            known = {i: next(iter(d)) for i, d in enumerate(rows) if len(d) == 1}
            self.fan(tree['fan'], known)
            self.leaves += 1
        elif kind == 'branch':
            vertex = tree['row']
            require(type(vertex) is int and 0 <= vertex < 8, 'Branch row')
            values = [entry[0] for entry in tree['children']]
            require(len(values) == len(set(values)) and set(values) == rows[vertex],
                    'Branch is not exhaustive over the current row domain')
            require(len(values) > 1, 'Branch must strictly split a non-singleton domain')
            for value, child in tree['children']:
                childrows = [d.copy() for d in rows]
                childrows[vertex] = {value}
                self.node(child, childrows, [d.copy() for d in cols])
        else:
            raise ValueError('Unsupported/incomplete tree node')

    def run(self):
        began = time.perf_counter()
        rows, cols = self.initial()
        self.node(self.cert['tree'], rows, cols)
        return {'case_id': self.cert['case_id'], 'status': 'EXCLUDED_BY_CHECKED_CSP_CERTIFICATE',
                'local_certificate_verified': True, 'full_search_verified': False,
                'nodes': self.nodes, 'leaves': self.leaves, 'deletions': self.deletions,
                'fan_witnesses_checked': self.fans, 'pair_rejections_checked': len(self.pairs),
                'seconds': time.perf_counter() - began}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cases', required=True)
    parser.add_argument('--certificates', nargs='+', required=True)
    parser.add_argument('--report', required=True)
    args = parser.parse_args()
    expected = {x['case_id']: x for x in json.loads(Path(args.cases).read_text(encoding='utf-8'))}
    paths = []
    for value in args.certificates:
        path = Path(value)
        paths.extend(sorted(path.parent.glob(path.name)) if '*' in value else [path])
    reports = []
    for path in paths:
        data = path.read_bytes()
        cert = json.loads(data)
        require(cert['case_id'] in expected, 'Unknown case ID')
        report = Checker(cert, expected[cert['case_id']]).run()
        report['certificate_sha256'] = hashlib.sha256(data).hexdigest()
        report['certificate_file'] = str(path)
        reports.append(report)
        print(json.dumps(report), flush=True)
        Path(args.report).write_text(json.dumps(reports, indent=2) + '\n', encoding='utf-8')


if __name__ == '__main__':
    main()
