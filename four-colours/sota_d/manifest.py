from replay_helpers import *
from collections import Counter
import hashlib,json,sys
p=Path(sys.argv[1]);bs=records(p/'unavoidable.conf');logs=p/'logs';dig=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
out={'size':len(bs),'rings':dict(sorted(Counter(int(b.splitlines()[1].split()[1]) for b in bs).items())),'sha256':{},'presentations':{},'reducer_shards':{}}
for n in ('unavoidable.conf','rules',*(f'p{d}' for d in range(5,13))):out['sha256'][n]=dig(p/n)
for d in range(5,13):
    s=(logs/f'p{d}.log').read_text();assert s.rstrip().endswith(' verified.') and f'Total of {len(bs)} configurations.' in s
    assert 'cannot do isomorphism verification' not in s
    status=logs/f'p{d}.status.json'
    if status.exists():assert json.loads(status.read_text())['exit']==0
    out['presentations'][f'p{d}']=s.splitlines()[-1]
covered=[]
layout=logs/'reduce-layout.json'
parts=[logs/f'part{k}.conf' for k in range(json.loads(layout.read_text())['shards'])] if layout.exists() else sorted(logs.glob('part*.conf'))
for part in parts:
    n=int(part.stem[4:]);batch=bs[n::len(parts)];assert part.read_text()=='\n\n'.join(batch)+'\n\n';s=(logs/f'reduce{n}.log').read_text()
    assert s.rstrip().endswith(f'Reducibility of {len(batch)} configurations verified') and s.count('***  D-reducible  ***')==len(batch)
    status=logs/f'reduce{n}.status.json'
    if status.exists():assert json.loads(status.read_text())['exit']==0
    covered+=batch;out['reducer_shards'][str(n)]=len(batch)
assert Counter(covered)==Counter(bs)
(p/'manifest.json').write_text(json.dumps(out,indent=2)+'\n')
