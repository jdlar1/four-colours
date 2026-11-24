from replay_helpers import *
from subprocess import run
import sys
b=Path(sys.argv[1]).resolve();od=b/'lift-check';od.mkdir(exist_ok=True)
r=run([base/'lift','../p12','../unavoidable.conf','../rules'],cwd=od,capture_output=True,text=True,check=True)
assert r.stdout.rstrip().endswith('verified.')
def offset(p,x):
    return ((p-1)%12-(x-1)+6)%12-6
images=[(int(x),int(i),int(p)) for s in r.stdout.splitlines() if s.startswith('I ') for _,x,i,p in [s.split()]]
assert images
image_offsets={offset(p,x) for x,i,p in images}
entries=(od/'outlet.et').read_text().strip().split('\n\n')
outlet_offsets={offset(int(line.split()[0]),1) for entry in entries for line in entry.splitlines()[1:]}
assert min(outlet_offsets|image_offsets)>=-4 and max(outlet_offsets|image_offsets)<=4
print('degree-12 outlet column offsets',sorted(outlet_offsets),'interior image offsets',sorted(image_offsets),'witness records',len({i for x,i,p in images}))
print('All spoke-relative supports lie strictly away from the opposite cut between offsets 5 and -6. No interior image contains the hub.')
