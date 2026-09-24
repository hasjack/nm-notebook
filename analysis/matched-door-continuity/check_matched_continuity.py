"""Independent trial-division and all-pairs check through 10,000."""
from pathlib import Path
from collections import defaultdict
from math import isqrt
import json,sys,subprocess,tempfile,shutil

def factors(n):
    out=set();d=2
    while d*d<=n:
        while n%d==0:out.add(d);n//=d
        d+=1
    if n>1:out.add(n)
    return out

def support(p):return factors(p+(1 if p%3==1 else -1))-{2}
ps=[p for p in range(5,10001,2) if all(p%q for q in range(2,isqrt(p)+1))]
records=[]
for p in ps:
 d=p+(1 if p%3==1 else -1);s=support(p);children=set()
 for q in s:children|=support(q)
 records.append((d,s,children,(len(s),5 in s,7 in s,max(s,default=1)**2>d)))
obs=[defaultdict(lambda:[0,0]),defaultdict(lambda:[0,0])];ctrl=[defaultdict(lambda:[0,0]),defaultdict(lambda:[0,0])]
def key(a,b):
 coarse=(b[0]-a[0],b[0].bit_length()-1)
 return coarse,coarse+a[3]+b[3]
for a,b in zip(records,records[1:]):
 if a[1]&b[1]:continue
 for level,k in enumerate(key(a,b)):
  obs[level][k][0]+=1;obs[level][k][1]+=bool(a[1]&b[2])
for i,a in enumerate(records):
 for b in records[i+2:]:
  if a[1]&b[1]:continue
  for level,k in enumerate(key(a,b)):
   if k in obs[level]:ctrl[level][k][0]+=1;ctrl[level][k][1]+=bool(a[1]&b[2])
here=Path(__file__).resolve().parent
with tempfile.TemporaryDirectory() as tmp:
 for n in ['matched_continuity.py','waits.py','ingredient_transitions.py']:shutil.copy(here/n,Path(tmp)/n)
 subprocess.run([sys.executable,str(Path(tmp)/'matched_continuity.py'),'--limit','10000'],check=True,stdout=subprocess.DEVNULL)
 data=json.loads((Path(tmp)/'matched-continuity.json').read_text())
 for index,s in enumerate(data['summaries']):
  level=index//3;minimum=s['min_controls_per_stratum'];n=hits=nc=0;expected=0.
  for k,(on,oh) in obs[level].items():
   cn,ch=ctrl[level].get(k,(0,0))
   if cn<minimum:continue
   n+=on;hits+=oh;nc+=cn;expected+=on*ch/cn
  assert (n,hits,nc)==(s['matched_observed'],s['observed_linked'],s['controls'])
  assert n==0 or abs(expected/n-s['standardized_control_rate'])<1e-12
print('Independent trial-division/all-pairs validation passed: all six matched comparisons through 10,000.')
