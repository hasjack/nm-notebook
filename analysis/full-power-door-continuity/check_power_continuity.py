"""Independent full-power census check through 10,000 using trial division."""
from pathlib import Path
from collections import Counter
from math import isqrt,prod
import tempfile,shutil,subprocess,sys,json

def factors(n):
    out={};q=2
    while q*q<=n:
        while n%q==0:out[q]=out.get(q,0)+1;n//=q
        q+=1
    if n>1:out[n]=out.get(n,0)+1
    return out

def door(p):return p+(1 if p%3==1 else -1)
primes=[p for p in range(5,10001,2) if all(p%q for q in range(2,isqrt(p)+1))]
c=Counter()
for a,b in zip(primes,primes[1:]):
    old=factors(door(a));old.pop(2,None);new=factors(door(b));new.pop(2,None)
    if old.keys()&new.keys():continue
    c['disjoint']+=1
    op=prod(q**e for q,e in old.items())
    whole=op>1 and any(door(r)%op==0 for r in new)
    c['whole_odd_part_preserved_all']+=whole
    c['nonempty_old_odd_part']+=op>1
    rep={q:e for q,e in old.items() if e>=2}
    if not rep:continue
    c['repeated_factor_opportunities']+=1
    c['repeated_factor_reconnects']+=any(door(r)%q==0 for q in rep for r in new)
    c['full_power_preserved']+=any(door(r)%(q**e)==0 for q,e in rep.items() for r in new)
    c['whole_odd_part_preserved_repeated']+=whole
here=Path(__file__).resolve().parent
with tempfile.TemporaryDirectory() as tmp:
    for n in ['power_continuity.py','waits.py','ingredient_transitions.py']:shutil.copy(here/n,Path(tmp)/n)
    subprocess.run([sys.executable,str(Path(tmp)/'power_continuity.py'),'--limit','10000'],check=True,stdout=subprocess.DEVNULL)
    d=json.loads((Path(tmp)/'power-continuity.json').read_text())
    assert dict(c)==d['counts'],(c,d['counts'])
full=json.loads((here/'power-continuity.json').read_text())
assert full['small_window']['opportunities']==c['repeated_factor_opportunities']
assert full['small_window']['linked']==c['repeated_factor_reconnects']
assert full['small_window']['full']==c['full_power_preserved']
assert full['small_window']['whole']==c['whole_odd_part_preserved_repeated']
for ex in full['examples']:
    assert all(factors(p)=={p:1} for p in (ex['previous_prime'],ex['prime']))
    for t in ex['paths']:
        assert door(t['arriving'])%(t['departing']**t['power'])==0
print('Independent trial-division check passed:',dict(c))
