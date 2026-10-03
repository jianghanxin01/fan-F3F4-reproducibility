"""Verify pinned data files and the forty published seed-pair identities.
Python standard library only. This is data binding, not a global UNSAT proof.
"""
import argparse
import bisect
import hashlib
import json
from pathlib import Path
import time

ENGINE = 'fan17-cpp-1'
DATASET = 'e38c0723b6a3be74'
TOTAL = 88294674
CHUNK = 500
SOURCE_ID = 'd5ad5bbd4b93f03e41cefb242c69f6f19db05d30b1729f607f84844430f1277c'
PINNED = {
    'catalog.json': ('f0e2cb9eeb3ace7c737d55cd001996d3dd010e98eb56b1ed94667a2d0aada050', 'c85356b27cb99c84'),
    'fan8_target17.graph6': ('453ae57ae9cb14d6cdc10c17d5735c0f4ad9a783aa1f45dddc122e96afcaa419', 'b9004989289e8545'),
    'fan9_target17.graph6': ('0832d8a3188519b1c717b84d209c08a3487ba6ac1ae1f0831bfeb59fe50f2cd3', 'd09ff1e67238a810'),
}
EXPECTED_CASE_IDS = [2050333, 2050335, 2050339, 2050340, 2050342, 2050346, 2050349, 2050350, 2058631, 2058632, 2058635, 2058636, 2058708, 2058788, 2059153, 7811134, 7811135, 7811138, 7811139, 7811140, 7811142, 7811146, 7811148, 7811149, 7811150, 7819431, 7819432, 7819434, 7819435, 7819436, 7819438, 7819953, 7819955, 7819958, 51996400, 64095209, 69103064, 69257548, 71867158, 82561944]

def require(condition, message):
    if not condition:
        raise ValueError(message)

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

def fnv(raw, initial=14695981039346656037):
    h = initial
    for byte in raw:
        h = ((h ^ byte) * 1099511628211) & ((1 << 64) - 1)
    return h

def decode_graph6(line, n):
    require(isinstance(line, str) and len(line) == 1 + (n * (n - 1) // 2 + 5) // 6,
            'Graph6 length mismatch')
    require(ord(line[0]) == 63 + n and all(63 <= ord(c) <= 126 for c in line), 'Graph6 encoding invalid')
    bits = [int(bool((ord(c) - 63) & (1 << shift))) for c in line[1:] for shift in range(5, -1, -1)]
    adj, index = [0] * n, 0
    for v in range(1, n):
        for u in range(v):
            if bits[index]:
                adj[u] |= 1 << v
                adj[v] |= 1 << u
            index += 1
    require(not any(bits[index:]), 'Nonzero graph6 padding')
    return adj

def compatible(a, b):
    if a[0] + b[0] > 10:
        return False
    if max(0, a[2], b[2]) > min(72, a[3], b[3]):
        return False
    if (a[4] & ~b[5]) or (b[4] & ~a[5]):
        return False
    if a[0] + b[0] == 10:
        if not ((b[7] & (1 << (2 - a[6]))) and (a[7] & (1 << (2 - b[6])))):
            return False
    return True

def check_inputs(cases_path, data_path):
    cases_path, data_path = Path(cases_path), Path(data_path)
    began = time.perf_counter()
    unresolved = [{'case':i,'task':i//CHUNK,'offset':i%CHUNK} for i in EXPECTED_CASE_IDS]
    rawdata = {name: (data_path / name).read_bytes() for name in PINNED}
    for name, raw in rawdata.items():
        require((sha(raw), '%016x' % fnv(raw)) == PINNED[name], 'Pinned dataset hash mismatch: ' + name)
    dataset_hash = fnv(rawdata['fan9_target17.graph6'], fnv(rawdata['fan8_target17.graph6'],
                       fnv(rawdata['catalog.json'], fnv(ENGINE.encode('ascii')))))
    require('%016x' % dataset_hash == DATASET, 'Dataset fingerprint mismatch')
    identity = json.loads((data_path / 'dataset_identity.json').read_bytes())
    require(identity['engine'] == ENGINE and identity['dataset'] == DATASET and identity['total_pairs'] == TOTAL
            and identity['source_manifest_id'] == SOURCE_ID and identity['chunk_size'] == CHUNK
            and identity['seed_counts'] == [8812, 115174] and identity['profile_counts'] == [6860, 60041]
            and identity['task_count'] == 176590, 'Dataset identity metadata mismatch')
    for name, prefix in [('catalog.json', 'catalog'), ('fan8_target17.graph6', 'left_graph6'),
                         ('fan9_target17.graph6', 'right_graph6')]:
        require((identity[prefix + '_sha256'], identity[prefix + '_fnv64']) == PINNED[name],
                'Dataset identity hash mismatch')
    catalog = json.loads(rawdata['catalog.json'])
    require(catalog['format'] == 'fan17-catalog-1' and catalog['orders'] == [8, 9]
            and catalog['total_pairs'] == TOTAL and catalog['source_manifest_id'] == SOURCE_ID,
            'Catalog identity mismatch')
    left_profiles, right_profiles = catalog['profiles_left'], catalog['profiles_right']
    prefix = [0]
    for row in left_profiles:
        prefix.append(prefix[-1] + row['pairs'])
    require(prefix[-1] == TOTAL, 'Catalog row total mismatch')
    lines = [rawdata[name].decode('ascii').splitlines() for name in ('fan8_target17.graph6', 'fan9_target17.graph6')]
    require(list(map(len, lines)) == [8812, 115174], 'Graph6 seed count mismatch')
    supplied = json.loads(cases_path.read_text(encoding='utf-8'))
    require(isinstance(supplied, list) and len(supplied) == 40, 'cases.json must contain forty entries')
    by_id = {}
    for case in supplied:
        require(type(case['case_id']) is int and case['case_id'] not in by_id, 'Duplicate or invalid supplied case ID')
        by_id[case['case_id']] = case
    require(set(by_id) == {r['case'] for r in unresolved}, 'Supplied cases do not equal exactly the forty UNKNOWN cases')
    rows = {}
    mappings = []
    for item in unresolved:
        case_id = item['case']
        i = bisect.bisect_right(prefix, case_id) - 1
        if i not in rows:
            blocks, local_prefix = [], [0]
            for j, right in enumerate(right_profiles):
                if compatible(left_profiles[i]['p'], right['p']):
                    blocks.append(j)
                    local_prefix.append(local_prefix[-1] + len(left_profiles[i]['ids']) * len(right['ids']))
            require(local_prefix[-1] == left_profiles[i]['pairs'], 'Independent catalog row count mismatch')
            rows[i] = blocks, local_prefix
        blocks, local_prefix = rows[i]
        local = case_id - prefix[i]
        block = bisect.bisect_right(local_prefix, local) - 1
        right_ids = right_profiles[blocks[block]]['ids']
        x, y = divmod(local - local_prefix[block], len(right_ids))
        indices = [left_profiles[i]['ids'][x], right_ids[y]]
        case = by_id[case_id]
        for key in ('case', 'task', 'offset'):
            if key in case:
                require(case[key] == item[key], 'Supplied case indexing field mismatch')
        for side, index in enumerate(indices):
            name = ('left', 'right')[side]
            require(case[name + '_index'] == index, 'Supplied seed index mismatch')
            g6 = lines[side][index]
            adj = decode_graph6(g6, 8 + side)
            require(case[name + '_red'] == adj, 'Supplied adjacency mismatch')
            if name + '_graph6' in case:
                require(case[name + '_graph6'] == g6, 'Supplied graph6 mismatch')
        mappings.append({'case_id': case_id, 'left_index': indices[0], 'right_index': indices[1]})

    return {'status':'DATA_AND_CASE_BINDING_VERIFIED','dataset':DATASET,
            'case_seed_bindings_checked':len(mappings),'case_seed_mappings':mappings,
            'independent_catalog_rows_checked':sorted(rows),'full_search_verified':False,
            'seconds':time.perf_counter()-began}

if __name__ == '__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    home=Path(__file__).resolve().parent.parent
    parser.add_argument('--data',type=Path,default=home/'data')
    parser.add_argument('--cases',type=Path,default=home/'certificates/cases.json')
    args=parser.parse_args()
    print(json.dumps(check_inputs(args.cases,args.data),indent=2))
