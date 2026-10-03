"""Prepare a new, orientation-aware 8+9 gluing catalog for order seventeen.

This prepares the fixed inputs and does not run the full SAT search.
Dependencies: igraph 1.0.0 for new canonical order-8 seeds, NumPy for weighted
profile counting. Use --data to select the generated-data directory.
"""
from __future__ import annotations
import argparse
import bisect
import collections
import hashlib
import importlib.util
import json
from pathlib import Path
import random
import sys
import time

HERE=Path(__file__).resolve().parent
DEFAULT_DATA=HERE.parent/'regenerated/data'
ENGINE='fan17-cpp-1'
CHUNK=500
TYPES=[(r,t,u) for r in range(9) for t in range(min(2,r//2)+1)
       for u in range(min(3,(8-r)//2)+1)]
TYPE_BIT={v:1<<i for i,v in enumerate(TYPES)}
assert len(TYPES)==49
FIELDS=['maximum_red_degree','red_edges','lower_cross_sum','upper_cross_sum',
        'center_type_support','opposite_center_types_allowed','maximum_root_red_matching','high_zero_flags']
PATTERN_TYPES={(k,x,y):sum(TYPE_BIT[(r,t,u)] for r,t,u in TYPES
                          if 7<=r+k<=10 and t+x<=2 and u+y<=3)
               for k in range(10) for x in range(3) for y in range(4)}

def sha(raw):return hashlib.sha256(raw).hexdigest()
def fnv(raw,h=14695981039346656037):
    for b in raw:h=((h^b)*1099511628211)&((1<<64)-1)
    return h
def emit(value):print(json.dumps(value,ensure_ascii=False),flush=True)
def write_json(path,value,compact=False):
    text=json.dumps(value,sort_keys=True,separators=(',',':') if compact else None,
                    indent=None if compact else 2,ensure_ascii=False)+'\n'
    raw=text.encode('utf-8')
    path.write_bytes(raw)
    return raw

def read_graph6(line):
    if isinstance(line,str):line=line.encode('ascii')
    n=line[0]-63
    if n not in (8,9) or len(line)!=1+(n*(n-1)//2+5)//6:
        raise ValueError('Expected compact order-eight or order-nine graph6')
    red=[0]*n;bit=0
    for v in range(1,n):
        for u in range(v):
            if (line[1+bit//6]-63)>>(5-bit%6)&1:red[u]|=1<<v;red[v]|=1<<u
            bit+=1
    return tuple(red)

def graph6(red):
    n=len(red);bits=[red[u]>>v&1 for v in range(1,n) for u in range(v)]
    bits += [0]*((-len(bits))%6)
    return bytes([n+63]+[63+sum(bits[i+j]<<(5-j) for j in range(6)) for i in range(0,len(bits),6)])

def matching_table(graph):
    table=bytearray(1<<len(graph))
    for mask in range(1,len(table)):
        bit=mask&-mask;v=bit.bit_length()-1;rest=mask^bit;best=table[rest];mates=graph[v]&rest
        while mates:
            bit=mates&-mates;mates^=bit
            best=max(best,1+table[rest^bit])
        table[mask]=best
    return table

def clique_table(graph):
    table=bytearray(1<<len(graph))
    for mask in range(1,len(table)):
        bit=mask&-mask;v=bit.bit_length()-1;rest=mask^bit
        table[mask]=max(table[rest],1+table[rest&graph[v]])
    return table

def extension_masks(red,return_tables=False):
    n=len(red);allmask=(1<<n)-1;blue=tuple(allmask^(1<<v)^red[v] for v in range(n))
    rm,bm=matching_table(red),matching_table(blue)
    rc,bc=clique_table(red),clique_table(blue)
    forbidden=[set(),set()]
    for color,(adj,table,cap) in enumerate(((red,rm,2),(blue,bm,3))):
        for u in range(n):
            for v in range(n):
                if adj[u]>>v&1 and table[adj[u]&~(1<<v)]>=cap:
                    forbidden[color].add((1<<u)|(1<<v))
    patterns=[]
    for mask in range(allmask+1):
        other=allmask^mask
        if rm[mask]>2 or bm[other]>3 or rc[mask]>=5 or bc[other]>=7:continue
        if any(mask&pair==pair for pair in forbidden[0]):continue
        if any(other&pair==pair for pair in forbidden[1]):continue
        patterns.append(mask)
    return (patterns,rm,bm) if return_tables else patterns

def seed_profile(red):
    n=len(red);other_order=17-n;allmask=(1<<n)-1
    patterns,rm,bm=extension_masks(red,True)
    degrees=[mask.bit_count() for mask in red];maximum=max(degrees);edges=sum(degrees)//2
    support=0
    for v,d in enumerate(degrees):support|=TYPE_BIT[(d,rm[red[v]],bm[allmask^(1<<v)^red[v]])]
    allowed=0;high=sum(1<<v for v,d in enumerate(degrees) if d==maximum);flags=0
    for mask in patterns:
        allowed|=PATTERN_TYPES[(mask.bit_count(),rm[mask],bm[allmask^mask])]
        if mask&high==0 and mask.bit_count()==maximum:
            for k in range(rm[mask],3):flags|=1<<k
    maximum_root=max(rm[red[v]] for v,d in enumerate(degrees) if d==maximum)
    return (maximum,edges,7*n-2*edges,sum(min(other_order,10-d) for d in degrees),
            support,allowed,maximum_root,flags)

def compatible(a,b):
    if a[0]+b[0]>10:return False
    if max(a[2],b[2],0)>min(72,a[3],b[3]):return False
    if a[4]&~b[5] or b[4]&~a[5]:return False
    if a[0]+b[0]==10 and (not b[7]&(1<<(2-a[6])) or not a[7]&(1<<(2-b[6]))):return False
    return True

def generate_eight(data,deps,canonical_source):
    target=data/'fan8_target17.graph6';record=data/'canonical8_target17_results.json'
    if target.is_file() and record.is_file():
        saved=json.loads(record.read_text(encoding='utf-8'));raw=target.read_bytes()
        if saved.get('seed_graph6_sha256')==sha(raw) and saved.get('complete_through')==8 and len(raw.splitlines())==8812:
            emit({'reuse_canonical_order8':8812});return saved
    if deps.is_dir():sys.path.insert(0,str(deps))
    # Load igraph before the historical module adds its old dependency paths.
    import igraph
    if igraph.__version__!='1.0.0':raise RuntimeError('This canonical release expects igraph 1.0.0')
    spec=importlib.util.spec_from_file_location('canonical_search17_backend',canonical_source)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    result,levels=module.enumerate_levels(8,target=17,audit=True)
    assert result['complete_through']==8 and len(levels[8])==8812
    raw=b''.join(graph6(red)+b'\n' for red in levels[8]);target.write_bytes(raw)
    result['seed_graph6_sha256']=sha(raw);result['seed_order']=8;write_json(record,result)
    return result

def profile_library(lines,side,np,data):
    cache=data/('profiles_'+side+'.npz');seed_hash=sha(b'\n'.join(lines)+b'\n')
    if cache.is_file():
        with np.load(cache,allow_pickle=False) as saved:
            if str(saved['seed_sha256'])==seed_hash and str(saved['profile_version'])=='fan17-profile8-1':
                signatures=saved['seed_profiles'].copy()
                elapsed=float(saved['elapsed_seconds']) if 'elapsed_seconds' in saved.files else None
                if elapsed is None:
                    previous=data/'preparation_report.json'
                    if previous.is_file():elapsed=json.loads(previous.read_text(encoding='utf-8')).get('profile_seconds_'+side)
                timing_path=data/('profiles_'+side+'_timing.json')
                if elapsed is None and timing_path.is_file():
                    timing=json.loads(timing_path.read_text(encoding='utf-8'))
                    if timing.get('seed_sha256')==seed_hash:elapsed=timing.get('original_build_seconds')
                write_json(timing_path,{'seed_sha256':seed_hash,'profile_version':'fan17-profile8-1',
                                      'original_build_seconds':elapsed,'current_run_reused_cache':True})
                emit({'reuse_profiles':side,'seeds':len(signatures),'original_build_seconds':elapsed})
                return [tuple(map(int,p)) for p in signatures],elapsed,True
    began=time.monotonic();signatures=[]
    for i,line in enumerate(lines):
        signatures.append(seed_profile(read_graph6(line)))
        if (i+1)%5000==0:emit({'profiling':side,'seeds':i+1,'total':len(lines),'elapsed_seconds':round(time.monotonic()-began,3)})
    elapsed=time.monotonic()-began
    np.savez_compressed(cache,seed_profiles=np.asarray(signatures,dtype=np.int64),
                        seed_sha256=np.asarray(seed_hash),profile_version=np.asarray('fan17-profile8-1'),
                        elapsed_seconds=np.asarray(elapsed))
    write_json(data/('profiles_'+side+'_timing.json'),{'seed_sha256':seed_hash,'profile_version':'fan17-profile8-1',
                  'original_build_seconds':elapsed,'current_run_reused_cache':False})
    return signatures,elapsed,False

def group_profiles(signatures):
    groups={}
    for idx,p in enumerate(signatures):groups.setdefault(p,[]).append(idx)
    return [{'p':list(p),'ids':ids} for p,ids in groups.items()]

def count_rows(left,right,np):
    a=np.asarray([p['p'] for p in left],dtype=np.int64);b=np.asarray([p['p'] for p in right],dtype=np.int64)
    wl=np.asarray([len(p['ids']) for p in left],dtype=np.int64);wr=np.asarray([len(p['ids']) for p in right],dtype=np.int64)
    counts=collections.Counter();counts['all_ordered_8x9_pairs']=int(wl.sum()*wr.sum());rows=[];began=time.monotonic()
    for first in range(0,len(left),32):
        aa=a[first:first+32];product=wl[first:first+32,None]*wr[None,:]
        ds=aa[:,0,None]+b[None,:,0];good=ds<=10
        counts['maximum_degree']+=int(np.sum(product,where=good))
        good &= np.maximum(np.maximum(aa[:,2,None],b[None,:,2]),0)<=np.minimum(np.minimum(72,aa[:,3,None]),b[None,:,3])
        counts['cross_sum_intervals']+=int(np.sum(product,where=good))
        good &= (aa[:,4,None]&~b[None,:,5])==0
        good &= (b[None,:,4]&~aa[:,5,None])==0
        counts['joint_center_types']+=int(np.sum(product,where=good))
        saturated=(b[None,:,7]&(1<<(2-aa[:,6,None])))>0
        saturated &= (aa[:,7,None]&(1<<(2-b[None,:,6])))>0
        good &= (ds!=10)|saturated
        current=np.sum(product,axis=1,where=good,dtype=np.int64)
        rows.extend(map(int,current));counts['saturated_boundary']+=int(current.sum())
        if first%512==0:emit({'counted_left_profiles':min(first+32,len(left)),'total_profiles':len(left),'elapsed_seconds':round(time.monotonic()-began,3)})
    for item,count in zip(left,rows):item['pairs']=count
    return dict(counts),time.monotonic()-began

def pair_lookup(catalog,case,cache):
    left=catalog['profiles_left'];right=catalog['profiles_right']
    prefix=cache.setdefault('prefix',[0])
    if len(prefix)==1:
        for item in left:prefix.append(prefix[-1]+item['pairs'])
    i=bisect.bisect_right(prefix,case)-1
    if i not in cache:
        js=[];bp=[0]
        for j,item in enumerate(right):
            if compatible(left[i]['p'],item['p']):js.append(j);bp.append(bp[-1]+len(left[i]['ids'])*len(item['ids']))
        assert bp[-1]==left[i]['pairs'];cache[i]=(js,bp)
    js,bp=cache[i];local=case-prefix[i];block=bisect.bisect_right(bp,local)-1;j=js[block]
    m,n=divmod(local-bp[block],len(right[j]['ids']))
    return [left[i]['ids'][m],right[j]['ids'][n]]

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--data',type=Path,default=DEFAULT_DATA)
    ap.add_argument('--deps',type=Path,default=HERE/'search17_deps')
    ap.add_argument('--source-nine',type=Path,default=HERE.parent/'data/fan9_target17.graph6',
                    help='Pinned 115174-seed order-nine graph6 library; its SHA-256 is checked.')
    ap.add_argument('--canonical-source',type=Path,default=HERE/'canonical_fans.py',
                    help='Canonical generation module; fan_search.py must be beside it.')
    args=ap.parse_args()
    if args.deps.is_dir():sys.path.insert(0,str(args.deps.resolve()))
    # Load NumPy before starting seed and profile generation.
    import numpy as np
    data=args.data.resolve();data.mkdir(parents=True,exist_ok=True);began=time.monotonic()
    canonical=generate_eight(data,args.deps.resolve(),args.canonical_source.resolve())
    raw9=args.source_nine.resolve().read_bytes()
    assert sha(raw9)=='0832d8a3188519b1c717b84d209c08a3487ba6ac1ae1f0831bfeb59fe50f2cd3'
    (data/'fan9_target17.graph6').write_bytes(raw9)
    raw8=(data/'fan8_target17.graph6').read_bytes();lines8=raw8.splitlines();lines9=raw9.splitlines()
    assert len(lines8)==8812 and len(lines9)==115174
    sig8,time8,reused8=profile_library(lines8,'left',np,data);sig9,time9,reused9=profile_library(lines9,'right',np,data)
    left=group_profiles(sig8);right=group_profiles(sig9);stages,counttime=count_rows(left,right,np)
    total=stages['saturated_boundary'];assert total>0
    source_manifest={'engine':ENGINE,'orders':[8,9],'total_order':17,'minimum_red_degree':7,'maximum_red_degree':10,
        'profile_version':'fan17-profile8-1','profile_fields':FIELDS,'types':TYPES,
        'left_graph6_sha256':sha(raw8),'right_graph6_sha256':sha(raw9),
        'canonical_backend':'igraph 1.0.0 / BLISS','canonical_seed_counts':[8812,115174]}
    source_manifest_id=sha(json.dumps(source_manifest,sort_keys=True,separators=(',',':')).encode())
    source_manifest['manifest_id']=source_manifest_id;write_json(data/'source_manifest.json',source_manifest)
    catalog={'format':'fan17-catalog-1','engine':ENGINE,'total_order':17,'orders':[8,9],
        'seed_counts':[8812,115174],'profile_counts':[len(left),len(right)],'profile_fields':FIELDS,
        'center_types':TYPES,'total_pairs':total,'chunk_size':CHUNK,'source_manifest_id':source_manifest_id,
        'profiles_left':left,'profiles_right':right}
    cat=write_json(data/'catalog.json',catalog,True)
    fingerprint=f'{fnv(raw9,fnv(raw8,fnv(cat,fnv(ENGINE.encode())))):016x}'
    identity={'engine':ENGINE,'dataset':fingerprint,'catalog_fnv64':f'{fnv(cat):016x}',
              'left_graph6_fnv64':f'{fnv(raw8):016x}','right_graph6_fnv64':f'{fnv(raw9):016x}',
              'catalog_sha256':sha(cat),'left_graph6_sha256':sha(raw8),'right_graph6_sha256':sha(raw9),
              'total_pairs':total,'seed_counts':[8812,115174],'profile_counts':[len(left),len(right)],
              'chunk_size':CHUNK,'task_count':(total+CHUNK-1)//CHUNK,'source_manifest_id':source_manifest_id}
    write_json(data/'dataset_identity.json',identity)
    header='// Generated by search17_prepare.py; pins the order-17 dataset.\n#pragma once\nnamespace fan_cli {\n'
    for name,key in [('EXPECTED_CATALOG_FNV','catalog_fnv64'),('EXPECTED_LEFT_FNV','left_graph6_fnv64'),
                     ('EXPECTED_RIGHT_FNV','right_graph6_fnv64'),('EXPECTED_DATASET','dataset')]:
        header+=f'inline constexpr const char* {name} = "{identity[key]}";\n'
    header+=f'inline constexpr unsigned long long EXPECTED_PAIRS = {total}ULL;\n'
    header+=f'inline constexpr unsigned EXPECTED_LEFT_PROFILES = {len(left)}U;\n'
    header+=f'inline constexpr unsigned EXPECTED_RIGHT_PROFILES = {len(right)}U;\n}}\n'
    (data.parent/'catalog_identity.hpp').write_text(header,encoding='utf-8')
    rng=random.Random(20261002)
    boundary_ids=[0,1,total-2,total-1]
    ids=boundary_ids+rng.sample(range(2,total-2),min(96,total-4));cache={}
    benchmark=[{'case':i,'seed_indices':pair_lookup(catalog,i,cache)} for i in ids]
    write_json(data/'benchmark_cases.json',benchmark)
    for i in [0,total-1]+rng.sample(range(total),min(100,total)):
        ai,bi=pair_lookup(catalog,i,cache);assert compatible(sig8[ai],sig9[bi])
    report={'format':'fan17-preparation-report-1','engine':ENGINE,'dataset':fingerprint,
        'orders':[8,9],'seed_counts':[8812,115174],'profile_counts':[len(left),len(right)],
        'seed_libraries_complete':[True,True],'profile_construction_complete':True,
        'weighted_catalog_count_complete':True,
        'count_stages':stages,'profile_seconds_left':time8,'profile_seconds_right':time9,
        'profile_cache_reused_left':reused8,'profile_cache_reused_right':reused9,
        'profile_time_semantics':'profile_seconds_* retain original profile-build timings; elapsed_seconds measures only this preparation invocation',
        'weighted_pair_count_seconds':counttime,'elapsed_seconds':time.monotonic()-began,
        'canonical8_record':canonical,'total_pairs':total,'task_count':identity['task_count'],'chunk_size':CHUNK,
        'benchmark_cases':len(benchmark),'benchmark_random_seed':20261002,
        'benchmark_selection':'first two and last two cases plus 96 uniformly sampled interior IDs, without replacement',
        'pair_index_scope':'rectangular ordered left-eight/right-nine; no triangular restriction or transpose identification',
        'nine_seed_reuse_reason':'the existing library imposes the same hereditary fan/clique exclusions valid at order at least 17',
        'source_manifest_id':source_manifest_id,'proof_verified':False,'full_search_run':False}
    write_json(data/'preparation_report.json',report);emit(report)

if __name__=='__main__':
    sys.stdout.reconfigure(encoding='utf-8');main()
