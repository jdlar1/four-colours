from pathlib import Path
import hashlib,tarfile
root=Path('steinberger')
with tarfile.open('source.tar') as tf:
 for p in sorted(root.iterdir()):
    raw=tf.extractfile('anc/'+p.name).read();assert raw==p.read_bytes();print(hashlib.sha256(raw).hexdigest(),p)
assert hashlib.sha256((root/'U_2822.conf').read_bytes()).hexdigest()=='61768599e85a45ff9bc884de06918d99c2c08cf68a6ad1048edd5d5f6f83c74d'
