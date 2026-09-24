"""Independent trial-division check of the <=100k gap census."""
import json
from collections import Counter,defaultdict
from pathlib import Path

def factors(n):
    fs=set();q=2
    while q*q<=n:
        while n%q==0:fs.add(q);n//=q
        q+=1
    if n>1:fs.add(n)
    return fs

def bucket(g):
    return '2–8' if g<=8 else '10–18' if g<=18 else '20–38' if g<=38 else '40–78' if g<=78 else '80+'

here=Path(__file__).resolve().parent
data=json.loads((here/'gap-ingredients.json').read_text())
counts=defaultdict(Counter);prev=None
for p in range(5,100001,2):
    if factors(p)!={p}:continue
    d=p+(1 if p%3==1 else -1);odd=factors(d)-{2}
    if prev:
        old,oldodd=prev;arr=max(odd-oldodd,default=0);c=counts[bucket(d-old)]
        c['pairs']+=1;c['large']+=arr*arr>d;c['none']+=arr==0
    prev=d,odd
for r in data['groups']:
    if r['band']!='<=100k':continue
    c=counts[r['gap_bin']]
    assert r['pairs']==c['pairs']
    assert r['no_new_odd_factor']==c['none']
    assert abs(r['arriving_above_sqrt_share']-c['large']/c['pairs'])<1e-12
assert sum(c['pairs'] for c in counts.values())==9589
print('Independent trial-division verification passed: all 9,589 transitions through 100,000.')
