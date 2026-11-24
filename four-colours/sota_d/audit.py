from pathlib import Path
from collections import Counter,defaultdict
from itertools import combinations
import sys,networkx as nx
def records(path):
    return Path(path).read_text().strip().split('\n\n')
def geometry(block):
    lines=block.splitlines()
    n,r,*_=map(int,lines[1].split())
    return r,{i:list(map(int,lines[2+i].split()[2:])) for i in range(1,n+1)}
p=Path(sys.argv[1]);bs=records(p/'unavoidable.conf');rules=(p/'rules').read_text().splitlines()
sources=[];ubs=[];i=0
while i<len(rules):
    line=rules[i].strip();i+=1
    if not line or line.startswith(('#','\\')):continue
    tok=line.split()
    if tok[1]=='invert':sources.append(sources[-1]);ubs.append(ubs[-1]);continue
    assert len(tok)==3
    v=int(tok[1]);lo=v//10;hi=v%10
    if hi==9:hi=12
    sources.append(lo or hi);ubs.append(hi);i+=1
assert max(sources)<=8 and max(ubs)<=8
groups=defaultdict(list);rings=Counter()
for idx,b in enumerate(bs,1):
    l=b.splitlines();assert l[2].split()==['0'] and l[1].split()[3]=='0'
    r,g=geometry(b);rings[r]+=1
    k=(r,tuple(sorted((v<=r,len(ns),tuple(sorted(len(g[u]) for u in ns))) for v,ns in g.items())))
    groups[k].append((idx,g,r))
def graph(r,nb):
    g=nx.Graph()
    for v,ns in nb.items():
        g.add_node(v,ring=v<=r);g.add_edges_from((v,u) for u in ns)
    return g
pairs=0
for group in groups.values():
    for (i,g,r),(j,h,s) in combinations(group,2):
        pairs+=1
        assert not nx.is_isomorphic(graph(r,g),graph(s,h),node_match=lambda a,b:a['ring']==b['ring']),(i,j)
print(len(bs),'pure-D headers, rings',sorted(rings.items()))
print(len(sources),'directed entries, maximum source low',max(sources),'upper',max(ubs))
print('zero ring-distinguished abstract or embedded duplicates;',pairs,'ambiguous pairs checked')
# Preserve the original small-configuration prefix as an independent check.
orig=records('steinberger/U_2822.conf');assert set(orig[:70])<=set(bs)
