"""Exact fan and clique helpers used by the canonical seed generator."""

def matchings(adj, mask, k, limit=1):
    out = []
    def rec(rem, need, selected):
        if len(out) >= limit:
            return
        if need == 0:
            out.append(tuple(selected))
            return
        if rem.bit_count() < 2 * need:
            return
        bit = rem & -rem
        v = bit.bit_length() - 1
        rest = rem ^ bit
        mates = adj[v] & rest
        while mates and len(out) < limit:
            b = mates & -mates
            mates ^= b
            u = b.bit_length() - 1
            rec(rest ^ b, need - 1, selected + [(v, u)])
        rec(rest, need, selected)
    rec(mask, k, [])
    return out

def violations(red, limit=1):
    n = len(red)
    allmask = (1 << n) - 1
    blue = [allmask ^ (1 << v) ^ red[v] for v in range(n)]
    out = []
    for col, adj, k in [('red', red, 3), ('blue', blue, 4)]:
        for v in range(n):
            for m in matchings(adj, adj[v], k, limit):
                out.append((col, v, m))
    return out

def cliques(adj, k, limit=16):
    out=[]
    def rec(candidates, chosen):
        if len(out)>=limit:
            return
        if len(chosen)==k:
            out.append(tuple(chosen))
            return
        if candidates.bit_count()<k-len(chosen):
            return
        while candidates and len(out)<limit:
            bit=candidates & -candidates
            candidates ^= bit
            v=bit.bit_length()-1
            rec(candidates & adj[v], chosen+[v])
    rec((1<<len(adj))-1,[])
    return out
