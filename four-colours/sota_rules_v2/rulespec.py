U=[0,0,0,1,0,3,2,1,4,3,8,3,0,0,5,6,15];V=[0,0,1,0,2,0,1,3,2,5,2,9,4,12,0,1,1]
def adj(d,deg):
    a={}
    def tri(x,y,z):a[x,y]=z;a[y,z]=x;a[z,x]=y
    for i in range(1,d+1):
        h=(i-2)%d+1;tri(0,h,i);tri(i,h,h+d)
        if deg[i][0]==deg[i][1] and deg[i][1]<=8:
            path=[h+d,*[k*d+i for k in range(2,deg[i][1]-3)],d+i]
            for v,w in zip(path,path[1:]):tri(i,v,w)
    return a
def code(lo,hi):
    if lo==hi:return str(lo)
    return f'{lo}{9 if hi==12 else hi}'

def rng(s):
    return (int(s[0]),int(s[-1]) if s[-1]!='9' else 12)
def polar_valid(source,sink,cond):
    for bounds,opp,flip in [(source,sink,0),(sink,source,1)]:
        for d in range(rng(bounds)[0],rng(bounds)[1]+1):
            spoke={i:(5,12) for i in range(1,d+1)};spoke[1]=rng(opp)
            pos={0:flip,1:1-flip};taken=set(pos.values())
            for j,b in cond:
                loc=adj(d,spoke).get((pos.get(U[j],-1),pos.get(V[j],-1)),-1)
                if loc<1 or loc in taken:return False
                taken.add(loc);pos[j]=loc
                if loc<=d:spoke[loc]=rng(b)
    return True

def entries(text):
    lines=iter(text.splitlines())
    for raw in lines:
        if not raw.strip() or raw.startswith('#'):continue
        parts=raw.split()
        if len(parts)==2 and parts[1]=='invert':
            yield int(parts[0]),None,None,[]
            continue
        n,src,sink=parts
        row=next(lines).split()
        if len(row)%2:raise ValueError("incomplete condition")
        yield int(n),src,sink,[(int(j),b) for j,b in zip(row[::2],row[1::2])]

def admissible(text):
    counts=[0]*13;ids=set();previous=None
    try:
        for n,s,t,cond in entries(text):
            if n<=0 or n in ids:return False
            ids.add(n)
            if s is None:
                if previous is None:return False
                s,t=previous;previous=None
            else:
                previous=(s,t)
                if len(dict(cond))!=len(cond) or any(j<2 or j>16 for j,_ in cond):return False
                for b in [s,t,*dict(cond).values()]:
                    lo,hi=rng(b)
                    if len(b)>2 or lo not in range(5,10) or hi not in (5,6,7,8,12) or lo>hi:return False
                if rng(s)[1]>8 or not polar_valid(s,t,cond):return False
            for b in (s,t):
                a,z=rng(b)
                for d in range(a,z+1):counts[d]+=1
        return max(counts)<=108
    except (KeyError,ValueError,IndexError,StopIteration):
        return False

# The template reflection fixes the directed transfer edge, swapping triangle sides.
_mirror={0:0,1:1}
for _j in range(2,len(U)):
    if U[_j] not in _mirror or V[_j] not in _mirror:continue
    _parents=(_mirror[V[_j]],_mirror[U[_j]])
    _image=next((k for k in range(2,len(U)) if (U[k],V[k])==_parents),None)
    if _image is not None:_mirror[_j]=_image
from functools import lru_cache
@lru_cache(maxsize=40000)
def _symmetric_tuple(cond):
    bounds=dict(cond)
    return all(_mirror.get(j) in bounds and bounds[_mirror[j]]==b for j,b in cond)
def self_reflecting(cond):
    """Check whether reflection across the directed edge preserves every guard."""
    return _symmetric_tuple(tuple(cond))
