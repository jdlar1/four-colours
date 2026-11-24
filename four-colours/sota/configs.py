from pathlib import Path
def records(p):
    return Path(p).read_text().strip().split('\n\n')
def geometry(block):
    rows=block.splitlines()
    n,r,*_=map(int,rows[1].split())
    return r,{i:list(map(int,rows[i+2].split()[2:])) for i in range(1,n+1)}
def canonical(block):
    r,g=geometry(block)
    codes=[]
    for start in range(1,r+1):
        for sign in (1,-1):
            ring=[1+(start-1+sign*i)%r for i in range(r)]
            labels={v:i for i,v in enumerate(ring)}
            queue=list(ring)
            rot={v:(g[v] if sign==1 else g[v][::-1]) for v in g}
            parents={}
            rows=[]
            for v in queue:
                a=rot[v]
                if v in parents:
                    i=a.index(parents[v]);a=a[i:]+a[:i]
                for u in a:
                    if u not in labels:
                        labels[u]=len(queue);queue.append(u);parents[u]=v
                rows.append(tuple(labels[u] for u in a))
            codes.append(tuple(rows))
    return min(codes)
def compatible(b):
    r,g=geometry(b)
    vs=set(g)-set(range(1,r+1))
    if 3*(len(g)-1)-r>=62:return False
    if any(len(set(g[v])-vs)>3 for v in vs):return False
    if max(map(len,g.values()))>12 or len(g)>26 or max(len(g[v]) for v in vs)>11 or sum(len(g[v])>8 for v in vs)>1:return False
    return any(vs<=set(g[v]).union({v},*(g[u] for u in g[v] if u in vs)) for v in vs)
def certified(inputpath,tsv):
    blocks=records(inputpath)
    for line in Path(tsv).read_text().splitlines():
        vals=list(map(int,line.split()))
        i,e,s,k=vals[:4]
        if k<0:continue
        rows=blocks[i].splitlines()
        rows[1]=' '.join(rows[1].split()[:2]+[str(e),str(s)])
        rows[2]=' '.join(map(str,vals[3:-1]))
        yield '\n'.join(rows)
