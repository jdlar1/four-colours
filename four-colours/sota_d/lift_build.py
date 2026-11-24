from pathlib import Path
import subprocess
s=Path('steinberger/discharge.c').read_text().replace('main(ac, av)','static int spoke;\nmain(ac, av)')
s=s.replace('      CheckBound(A, posout, s, v[i], 0, 0, lineno, print);','''      if(x[i]!=y[i]||v[i]!=5)abort();spoke=x[i];
      CheckBound(A, posout, s, v[i], 0, 0, lineno, print);''')
s=s.replace('      /* Double-check isomorphism */','''      for(i=redring+1;i<=redverts;i++){
          int u=image[i]; if(u<=0)abort();printf("I %d %d %d\\n",spoke,h+1,u);
      }''')
Path('lift.c').write_text(s)
subprocess.run('gcc -O3 -w -std=gnu89 lift.c -o lift'.split(),check=True)
