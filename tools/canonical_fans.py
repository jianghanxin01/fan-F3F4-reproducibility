"""Isomorph-free vertex augmentation for (F3,F4)-free red graphs.

Generation uses parent automorphism orbits on neighbourhood subsets and a
canonical deletion orbit in each child. There are no pairwise graph-isomorphism
tests and no canonical-form hash table in the generation algorithm.
igraph/BLISS supplies canonical permutations and automorphism generators.
The independent validation below may use canonical forms to audit duplicates.
"""
import argparse
import json
from pathlib import Path
import random
import sys
import time

sys.stdout.reconfigure(encoding='utf-8')
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import igraph as ig
from fan_search import violations, cliques


def graph(red):
    return ig.Graph(n=len(red), edges=[(i,j) for i in range(len(red))
                                     for j in range(i+1,len(red))
                                     if red[i] & (1 << j)])


def image_mask(mask, permutation):
    result = 0
    while mask:
        bit = mask & -mask
        mask ^= bit
        result |= 1 << permutation[bit.bit_length()-1]
    return result


def subset_representatives(n, generators):
    """Exactly one neighbourhood mask per Aut(parent)-orbit."""
    seen = bytearray(1 << n)
    for mask in range(1 << n):
        if seen[mask]:
            continue
        seen[mask] = 1
        stack = [mask]
        while stack:
            current = stack.pop()
            for permutation in generators:
                other = image_mask(current, permutation)
                if not seen[other]:
                    seen[other] = 1
                    stack.append(other)
        yield mask


def canonical_deletion_accepts(child):
    """The new vertex must lie in the child's canonical deletion orbit."""
    n = child.vcount()
    permutation = child.canonical_permutation()
    # igraph 1.0 permute_vertices uses new-to-old order. Read its actual
    # permutation convention, not the contradictory canonical_permutation
    # docstring retained in this release. Validation checks full atlas counts.
    chosen = permutation[n-1]  # old vertex bearing the last canonical label
    if chosen == n-1:
        return True
    parents = list(range(n))
    def root(x):
        while parents[x] != x:
            parents[x] = parents[parents[x]]
            x = parents[x]
        return x
    for generator in child.automorphism_group():
        for i,j in enumerate(generator):
            parents[root(i)] = root(j)
    return root(chosen) == root(n-1)


def canonical_key(red):
    g = graph(red)
    canonical = g.permute_vertices(g.canonical_permutation())
    return tuple(sorted(tuple(sorted(edge)) for edge in canonical.get_edgelist()))


def enumerate_levels(max_order, fan_free=True, target=None, seconds=None,
                     audit=False):
    """Completed levels are exhaustive; an interrupted level is marked partial.

    target>=17 restricts partial graphs to necessary extendibility conditions:
    red degree<=10, blue degree<=9, no blue K8 and no red K6. Target minimum degrees are
    never imposed on a smaller partial graph.
    """
    if target is not None and (not fan_free or target < 17 or max_order > target):
        raise ValueError('target mode requires fan_free and target>=max(17,max_order)')
    start = time.monotonic()
    levels = [{'order':0, 'count':1, 'complete':True}]
    current = [()]
    all_levels = [current]
    stopped = False
    for n in range(max_order):
        children = []
        examined = 0
        for red in current:
            parent = graph(red)
            for mask in subset_representatives(n, parent.automorphism_group()):
                if seconds is not None and time.monotonic()-start >= seconds:
                    stopped = True
                    break
                examined += 1
                child_red = tuple(red[i] | ((1 << n) if mask & (1 << i) else 0)
                                  for i in range(n)) + (mask,)
                if target is not None:
                    if any(a.bit_count()>10 or n-a.bit_count()>9 for a in child_red):
                        continue
                    full = (1 << (n+1))-1
                    blue = [full ^ (1 << i) ^ a for i,a in enumerate(child_red)]
                    if cliques(blue,8,1) or cliques(child_red,6,1):
                        continue
                if fan_free and violations(child_red):
                    continue
                if canonical_deletion_accepts(graph(child_red)):
                    children.append(child_red)
            if stopped:
                break
        if audit:
            keys = {canonical_key(red) for red in children}
            assert len(keys) == len(children), 'duplicate isomorphism class'
        result = {'order':n+1,'count':len(children),'complete':not stopped,
                  'extension_orbit_representatives_examined':examined,
                  'elapsed_seconds':round(time.monotonic()-start,3)}
        levels.append(result)
        print(json.dumps(result),flush=True)
        all_levels.append(children)
        if stopped:
            break
        current = children
    return {'method':'canonical construction path with automorphism subset orbits',
            'backend':'igraph '+ig.__version__+' / BLISS',
            'fan_free':fan_free,'target_order':target,
            'complete_through':max(x['order'] for x in levels if x['complete']),
            'levels':levels}, all_levels


def validate():
    import networkx as nx
    rng = random.Random(20260929)
    for n in range(1,10):
        for trial in range(20):
            edges = [(i,j) for i in range(n) for j in range(i+1,n)
                     if rng.random()<0.5]
            g = ig.Graph(n=n,edges=edges)
            p = list(range(n))
            rng.shuffle(p)
            h = g.permute_vertices(p)
            def canon(g):
                c = g.permute_vertices(g.canonical_permutation())
                return tuple(sorted(tuple(sorted(e)) for e in c.get_edgelist()))
            assert canon(g) == canon(h)
            for generator in g.automorphism_group():
                assert {tuple(sorted((generator[i],generator[j]))) for i,j in edges} == set(edges)
    result, levels = enumerate_levels(6,fan_free=False,audit=True)
    known = [1,1,2,4,11,34,156]
    assert [x['count'] for x in result['levels']] == known
    atlas = nx.graph_atlas_g()
    admissible_counts = [0]*8
    for g in atlas:
        n = len(g)
        red = tuple(sum(1 << j for j in g.neighbors(i)) for i in range(n))
        if not violations(red):
            admissible_counts[n] += 1
    fans, levels = enumerate_levels(7,fan_free=True,audit=True)
    assert [x['count'] for x in fans['levels']] == admissible_counts
    validation = {'unrestricted_counts_through_6':known,
                  'fan_free_counts_from_independent_graph_atlas':admissible_counts,
                  'fan_free_counts_from_canonical_augmentation':
                  [x['count'] for x in fans['levels']],
                  'random_canonical_relabelling_checks':180,
                  'no_duplicate_classes_in_audited_levels':True,
                  'backend':fans['backend']}
    (HERE/'canonical_validation.json').write_text(json.dumps(validation,indent=2))
    print(json.dumps(validation),flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--validate',action='store_true')
    parser.add_argument('--max-order',type=int,default=8)
    parser.add_argument('--seconds',type=float)
    parser.add_argument('--target',type=int)
    parser.add_argument('--audit',action='store_true')
    parser.add_argument('--export',type=Path,help='Write final completed level as graph6')
    args = parser.parse_args()
    if args.validate:
        validate()
    else:
        record, levels = enumerate_levels(args.max_order,target=args.target,
                                         seconds=args.seconds,audit=args.audit)
        tag = '_target'+str(args.target) if args.target is not None else ''
        (HERE/('canonical'+tag+'_results.json')).write_text(json.dumps(record,indent=2))
        if args.export is not None:
            if record['complete_through'] != args.max_order:
                raise RuntimeError('Refusing to export an incomplete level as a seed library')
            if args.max_order > 62:
                raise ValueError('Compact graph6 writer supports orders at most 62')
            with args.export.open('wb') as f:
                for red in levels[-1]:
                    n = len(red)
                    bits = [(red[i] >> j) & 1 for j in range(1,n) for i in range(j)]
                    bits += [0]*((-len(bits))%6)
                    chars = [n+63] + [63+sum(bits[i+j] << (5-j) for j in range(6))
                                             for i in range(0,len(bits),6)]
                    f.write(bytes(chars)+b'\n')
