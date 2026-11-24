"""Replay the 633 one-per-configuration positive witnesses and their charge sums."""
import subprocess,tempfile
from collections import defaultdict
from pathlib import Path
base=Path(__file__).resolve().parent
byhub=defaultdict(list)
for line in (base/'private-witnesses.tsv').read_text().splitlines()[1:]:
    i,d,q,w=line.split('\t');byhub[int(d)].append((int(i),int(q),w))
assert sorted(i for rs in byhub.values() for i,q,w in rs)==list(range(1,634))
with tempfile.TemporaryDirectory(dir=base) as tmp:
    p=Path(tmp)
    (p/'rules').symlink_to(base/'../recon/rsst/rules')
    (p/'unavoidable.conf').write_bytes((base/'../recon/rsst/unavoidable.conf').read_bytes()+(base/'../recon/33333.conf').read_bytes())
    for d,rs in sorted(byhub.items()):
        (p/'axles').write_text(''.join(w+'\n' for i,q,w in rs))
        subprocess.run([base/'concrete_check',str(d),'1','axles'],cwd=p,stdout=subprocess.DEVNULL,check=True)
        assert (p/'positive.tsv').read_text().splitlines()==[f'{n} 0 {q} {i}' for n,(i,q,w) in enumerate(rs)]
    subprocess.run([base/'audit_private',p/'unavoidable.conf',base/'private-witnesses.tsv'],check=True)
print('All 633 positive charges and all 633 unique witnesses reproduced.')
