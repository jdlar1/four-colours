from pathlib import Path
import subprocess, sys, concurrent.futures, json
base=Path.cwd()
directory=Path(sys.argv[1]).resolve()
jobs=int(sys.argv[2])
assert 1<=jobs<=8
mode=sys.argv[3]
logs=directory/'logs'
logs.mkdir(exist_ok=True)
def check(args,cwd,suffix,end,ds=None):
    cwd.mkdir(exist_ok=True,parents=True)
    out=subprocess.run(args,cwd=cwd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    (logs/(suffix+'.log')).write_bytes(out.stdout)
    (logs/(suffix+'.status.json')).write_text(json.dumps({'argv':list(map(str,args)),'exit':out.returncode,'last_line':out.stdout.decode(errors='replace').splitlines()[-1:]} )+'\n')
    assert out.returncode==0 and out.stdout.rstrip().endswith(end.encode()),(suffix,out.returncode,out.stdout[-300:])
    if ds is not None: assert out.stdout.count(b'***  D-reducible  ***')==ds
    print(suffix,'EXIT=0',flush=True)
def pres(d):
    pres_name=f'../../p{d}'
    check([base/'discharge',pres_name,'../../unavoidable.conf','../../rules'],logs/f'hub{d}',f'p{d}',f'{pres_name} verified.')
def red(k):
    records=(directory/'unavoidable.conf').read_text().strip().split('\n\n')[k::jobs]
    assert records and all(r.splitlines()[1].split()[3]=='0' and r.splitlines()[2].split()==['0'] for r in records)
    path=logs/f'part{k}.conf'
    path.write_text('\n\n'.join(records)+'\n\n')
    check([base/'reduce',path],logs,f'reduce{k}',f'Reducibility of {len(records)} configurations verified',len(records))
with concurrent.futures.ThreadPoolExecutor(jobs) as pool:
    if mode in ('discharge','both'):list(pool.map(pres,range(5,13)))
    if mode in ('reduce','both'):
        list(pool.map(red,range(jobs)))
        (logs/'reduce-layout.json').write_text(json.dumps({'shards':jobs})+'\n')
