"""Independent trial-division verification of every classified swallow."""
from pathlib import Path
from math import isqrt,prod
import json

def factors(n):
    out={};q=2
    while q*q<=n:
        while n%q==0:out[q]=out.get(q,0)+1;n//=q
        q+=1
    if n>1:out[n]=out.get(n,0)+1
    return out

def prime(n):return n>=2 and all(n%q for q in range(2,isqrt(n)+1))
def door(p):return p+(1 if p%3==1 else -1)
p=Path(__file__).resolve().parent/'swallow-shape.json';d=json.loads(p.read_text())
for e in d['events']:
    a,b=e['previous_prime'],e['prime']
    assert prime(a) and prime(b) and not any(prime(n) for n in range(a+1,b))
    assert door(a)==e['previous_door'] and door(b)==e['door']
    old=factors(door(a));old.pop(2,None);new=factors(door(b));new.pop(2,None)
    A=prod(q**v for q,v in old.items())
    assert A==e['A'] and any(v>=2 for v in old.values()) and not old.keys()&new.keys()
    actual=[r for r in new if door(r)%A==0]
    assert sorted(actual)==sorted(w['r'] for w in e['witnesses'])
    for w in e['witnesses']:
        assert prime(w['r']) and door(w['r'])==w['door']
        h=door(w['r'])//A;assert h==w['quotient'] and h==2**w['k']*w['B']
        assert w['pure']==(w['B']==1)
        if w['pure']:
            C=door(b)//w['r']
            assert C&(C-1)==0 and door(a)==C*door(w['r']) and door(b)-door(a)==C
            assert w['r']%3==2
assert len(d['events'])==d['counts']['transitions']
print(f"Independent verification passed for all {len(d['events']):,} transitions: prime endpoints, consecutiveness, odd blocks, exhaustive witnesses, quotients and normal form.")
