"""Stock replay, inventory, rooted-triangulation and abstract isomorphism audits."""
import os
from collections import Counter,defaultdict
from hashlib import sha256
from itertools import combinations
from pathlib import Path
import argparse,json,subprocess,tempfile,re,sys
from rulespec import rng,polar_valid,entries,admissible,self_reflecting
root=Path(__file__).resolve().parent
sys.dont_write_bytecode=True
def blocks(path):return path.read_text().strip().split("\n\n")
sys.path.insert(0,str(root/'../sota'))
from configs import canonical,geometry
import networkx as nx
def degree12_trace(binary, directory, configurations):
    trace = subprocess.run([binary, 'present12', '2', '4'], cwd=directory,
                           check=True, capture_output=True, text=True).stdout
    assert trace.rstrip().endswith('present12 verified.')
    assert 'cannot do isomorphism verification' not in trace
    edge = None
    reductions = Counter()
    branches = 0
    interior_offsets = set()
    traced_offsets = set()
    for line in trace.splitlines():
        member = re.fullmatch(r'-->Checking hubcap member \((\d+),(\d+),5\)', line)
        if member:
            edge = int(member[1])
            assert int(member[2]) == edge
            reductions[edge] += 0
        if line.startswith('Lowering upper bound of vertex'):
            branches += 1
        if not line.startswith('Conf('):
            continue
        record, positions = line.split(':')
        section, row, column = map(int, re.findall(r'\d+', record))
        index = (section - 1) * 70 + (row - 1) * 7 + column - 1
        vertices, ring = map(int, configurations[index].splitlines()[1].split()[:2])
        images = {int(vertex): int(position)
                  for position, vertex in re.findall(r'(\d+)\((\d+)\)', positions)}
        assert all(v in images and images[v] != 0 for v in range(ring + 1, vertices + 1))
        reductions[edge] += 1
        for vertex, position in images.items():
            if position == 0:
                continue  # An auxiliary ring image can coincide with the hub.
            offset = (position - edge + 6) % 12 - 6
            traced_offsets.add(offset)
            if vertex > ring:
                interior_offsets.add(offset)
    assert set(reductions) == set(range(1, 13))
    assert traced_offsets <= set(range(-2, 3))
    return dict(reductions_by_edge=dict(sorted(reductions.items())),
                interior_offsets=sorted(interior_offsets),
                all_nonhub_image_offsets=sorted(traced_offsets),
                recursive_upper_bound_decreases=branches)

def audit(src):
    if not __debug__:raise RuntimeError('Run without Python optimization to enable all audit checks')
    stock=root/'../recon/rsst';out=root/os.getenv('AUDIT_DIR','verification');out.mkdir(exist_ok=True)
    cfg=blocks(src/'unavoidable.conf');N=len(cfg)
    assert N==len(set(map(canonical,cfg)))
    gs=defaultdict(list);ring=Counter();maxinner=0
    for i,b in enumerate(cfg,1):
        r,adj=geometry(b);assert r<=14
        k=int(b.splitlines()[2].split()[0])
        assert (int(b.splitlines()[1].split()[3])==0)==(k==0)
        ring[r,'C' if k else 'D']+=1
        key=(r,tuple(sorted((v<=r,len(nb),tuple(sorted(len(adj[u]) for u in nb))) for v,nb in adj.items())))
        g=nx.Graph()
        for v,nb in adj.items():
            g.add_node(v,ring=v<=r); g.add_edges_from((v,u) for u in nb)
            if v>r:maxinner=max(maxinner,len(nb))
        gs[key].append(g)
    pairs=0
    for bucket in gs.values():
        for g,h in combinations(bucket,2):
            pairs+=1
            assert not nx.is_isomorphic(g,h,node_match=lambda a,b:a['ring']==b['ring'])
    ids=set();prev=False;rule_audit=[];lines=iter((src/'rules').read_text().splitlines())
    for raw in lines:
        if not raw.strip() or raw.startswith('#'):continue
        line=raw.split();n=int(line[0]);assert n>0 and n not in ids;ids.add(n)
        if line[1]=='invert':
            assert prev and n==rule_audit[-1]['id']+1
            prev=False;rule_audit[-1]['inverted']=True;continue
        prev=True
        _,s,t=line;parts=next(lines).split();assert len(parts)%2==0
        c=[(int(j),b) for j,b in zip(parts[::2],parts[1::2])]
        assert len(dict(c))==len(c) and all(2<=j<=16 for j,_ in c)
        for b in [s,t,*dict(c).values()]:
            lo,hi=rng(b);assert lo in (5,6,7,8,9) and hi in (5,6,7,8,12) and lo<=hi
        assert rng(s)[0]<=8 and rng(s)[1]<=8
        assert polar_valid(s,t,c),(n,s,t,c)
        rule_audit.append(dict(id=n,src=s,sink=t,inverted=False))
    assert admissible((src/'rules').read_text())
    stock_unpaired={n:(s,t,tuple(c)) for n,s,t,c in entries((stock/'rules').read_text()) if n in (21,26,63)}
    unpaired={r['id'] for r in rule_audit if not r['inverted']}
    identities={n:(s,t,tuple(c)) for n,s,t,c in entries((src/'rules').read_text()) if n in unpaired}
    assert all(self_reflecting(c) for s,t,c in identities.values())
    res=dict(count=N,embedded_distinct=N,abstract_distinct=N,ambiguous_abstract_pairs=pairs,
             D=sum(v for (r,t),v in ring.items() if t=='D'),C=sum(v for (r,t),v in ring.items() if t=='C'),
             ring={r:[ring[r,'D'],ring[r,'C']] for r in sorted({r for r,_ in ring})},
             maximum_interior_degree=maxinner,rule_entries=len(ids),explicit_inversions=sum(r['inverted'] for r in rule_audit),
             sha256={n:sha256((stock/n).read_bytes()).hexdigest() for n in ['reduce.c','discharge.c']},runs={},outlets={})
    src=src.resolve()
    with tempfile.TemporaryDirectory(dir=out) as tmp:
        tmp=Path(tmp)
        for op in ['reduce','discharge']:
            subprocess.run(['gcc','-std=gnu89','-O3','-w',stock/(op+'.c'),'-o',tmp/op],check=True)
        for name in ['rules','unavoidable.conf',*(f'present{i}' for i in range(5,13))]:
            (tmp/name).symlink_to(src/name)
            res['sha256'][name]=sha256((src/name).read_bytes()).hexdigest()
        for d in [*range(5,13),0]:
            name=f'present{d}' if d else 'unavoidable.conf';op='discharge' if d else 'reduce'
            q=subprocess.run([tmp/op,name],cwd=tmp,capture_output=True,text=True)
            end=q.stdout.strip().splitlines()[-1]
            (out/f'{name}.log').write_text(q.stdout+q.stderr)
            assert 'cannot do isomorphism verification' not in q.stdout
            assert q.returncode==0 and end==(f'{name} verified.' if d else f'Reducibility of {N} configurations verified')
            res['runs'][name]=dict(exit=q.returncode,last_line=end)
            if d:res['outlets'][d]=int(re.search(r'in (\d+) outlets',q.stdout)[1]);assert res['outlets'][d]<=108
            if d==12:
                offsets=set()
                for block in (tmp/'outlet.et').read_text().strip().split('\n\n'):
                    header,*bounds=block.splitlines()
                    assert int(header.split()[1])==1
                    for row in bounds:offsets.add(((int(row.split()[0])-1+6)%12)-6)
                res['degree12_spoke_offsets']=sorted(offsets)
                assert offsets <= set(range(-2,3)) and maxinner < 12
                assert (src/"present12").read_text().splitlines() == ["Degree 12", "L0 H " + " ".join(f"({i},{i},5)" for i in range(1,13)), "Q.E.D."]
                res['degree12_stock_trace'] = degree12_trace(tmp/'discharge', tmp, cfg)
    res.update(maximum_ring=max(r for r,t in ring),maximum_source_upper_degree=max(rng(r['src'])[1] for r in rule_audit),
               maximum_outlet_count=max(res['outlets'].values()),unpaired_stock_entries=sorted(n for n,r in identities.items() if stock_unpaired.get(n)==r),
               intrinsically_symmetric_entries=sorted(unpaired),
               ring_count_order=['D','C'],degree12_single_edge_bound_tenths=5,
               degree12_single_edge_obligations=12,degree12_positive_outlets_only=True)
    (out/'summary.json').write_text(json.dumps(res,indent=2)+'\n');print(json.dumps(res),flush=True)
if __name__=='__main__':audit(Path(sys.argv[1]))
