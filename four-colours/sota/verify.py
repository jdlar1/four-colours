"""Rebuild the unmodified stock programs, replay a bundle, and audit its inventory."""
from collections import Counter
from configs import canonical,records
from hashlib import sha256
from pathlib import Path
import subprocess,sys,tempfile,json
root=Path(__file__).resolve().parent
stock=root.parent/'recon/rsst'
bundle=Path(sys.argv[1]).resolve()
logs=root/'verification'/bundle.name
logs.mkdir(parents=True,exist_ok=True)
def digest(p):return sha256(p.read_bytes()).hexdigest()
bs=records(bundle/'unavoidable.conf')
assert digest(bundle/'rules')==digest(stock/'rules')
seen={canonical(b) for b in bs}
assert len(seen)==len(bs)
table=Counter()
contracts=Counter()
for b in bs:
    lines=b.splitlines()
    n,r,e,s=map(int,lines[1].split());k=int(lines[2].split()[0])
    assert r<=14 and (s==0)==(k==0)
    table[r,'D' if k==0 else 'C']+=1;contracts[k]+=1
res={'count':len(bs),'distinct':len(seen),'D':contracts[0],
     'C':len(bs)-contracts[0],'ring':{r:[table[r,'D'],table[r,'C']] for r in sorted({r for r,_ in table})},
     'contract_sizes':dict(sorted(contracts.items())),'sha256':{p:digest(stock/p) for p in ('rules','discharge.c','reduce.c')},
     'preserved_high_degree_lemma_indices':[i for i in [1,3,6,9,24,26,139,324] if records(stock/'unavoidable.conf')[i-1] in bs],
     'runs':{}}
with tempfile.TemporaryDirectory(dir=logs) as scratch:
    run=Path(scratch)
    for name in ('reduce','discharge'):
        subprocess.run(['gcc','-std=gnu89','-w','-O3',stock/(name+'.c'),'-o',run/name],check=True)
    for file in ['unavoidable.conf','rules',*(p.name for p in bundle.glob('present*') if p.name[7:].isdigit())]:
        (run/file).symlink_to(bundle/file)
    tests=[('reduce','unavoidable.conf',f'Reducibility of {len(bs)} configurations verified')]
    tests.extend(('discharge',p.name,f'{p.name} verified.') for p in sorted(run.glob('present*'),key=lambda p:int(p.name[7:])))
    for cmd,arg,end in tests:
        p=subprocess.run([run/cmd,arg],cwd=run,capture_output=True,text=True)
        out=logs/(cmd+'-'+arg+'.log');out.write_text(p.stdout+p.stderr)
        assert p.returncode==0 and p.stdout.rstrip().endswith(end),(p.returncode,out)
        res['runs'][f'{cmd} {arg}']={'exit':p.returncode,'last_line':end}
(logs/'summary.json').write_text(json.dumps(res,indent=2)+'\n')
print(json.dumps(res))
