#!/usr/bin/env python3
"""Classify whole-odd-part preservation within the repeated-factor cohort."""
from waits import sieve
from ingredient_transitions import fac
from pathlib import Path
from collections import Counter
from math import prod
import argparse,json

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--limit',type=int,default=10000000);X=ap.parse_args().limit
 spf=sieve(X+1);prev=None;events=[];counts=Counter();ks=Counter();bs=Counter();mult=Counter();pureks=Counter()
 for p in range(5,X+1,2):
  if spf[p]:continue
  d=p+(1 if p%3==1 else -1);f=fac(d,spf);odd={q:e for q,e in f.items() if q!=2}
  if prev:
   a,old,oldfs,A=prev
   if any(e>=2 for e in oldfs.values()) and not (odd.keys()&oldfs.keys()):
    witnesses=[]
    for r in odd:
     rd=r+(1 if r%3==1 else -1)
     if rd%A:continue
     quotient=rd//A;k=0;B=quotient
     while B%2==0:k+=1;B//=2
     assert k>=1 and B%2==1 and B%3 and rd==(2**k)*A*B
     assert (r-2**k*A*B)==-(1 if r%3==1 else -1)
     pure=B==1
     w=dict(r=r,door=rd,quotient=quotient,k=k,B=B,pure=pure,extra_odd_factors=fac(B,spf) if B>1 else {})
     witnesses.append(w);counts['witnesses']+=1;counts['pure_witnesses']+=pure
     ks[k]+=1;bs[B]+=1
     if pure:pureks[k]+=1
    if witnesses:
     np=sum(w['pure'] for w in witnesses);nw=len(witnesses)
     counts['transitions']+=1;counts['pure_transitions']+=bool(np)
     counts['pure_only']+=np==nw;counts['extra_only']+=np==0;counts['both_types']+=0<np<nw
     mult[nw]+=1
     events.append(dict(previous_prime=a,prime=p,previous_door=old,door=d,A=A,A_factors=oldfs,witnesses=witnesses))
  A=prod(q**e for q,e in odd.items());prev=(p,d,odd,A)
 assert counts['pure_only']+counts['extra_only']+counts['both_types']==counts['transitions']
 assert sum(mult.values())==counts['transitions'] and sum(n*c for n,c in mult.items())==counts['witnesses']
 here=Path(__file__).resolve().parent
 if X==10000000:
  previous=json.loads((here/'power-continuity.json').read_text())
  assert counts['transitions']==previous['counts']['whole_odd_part_preserved_repeated']==1336
 data=dict(limit=X,counts=dict(counts),witness_multiplicity=dict(mult),all_k=dict(ks),pure_k=dict(pureks),extra_odd_multiplier_counts=dict(bs),events=events)
 normal=Counter();gap_counts=Counter()
 for event in events:
  for w in event['witnesses']:
   C=event['door']//w['r']
   fits=(C>0 and C&(C-1)==0 and w['pure'] and event['previous_door']==C*w['door'] and w['r']%3==2)
   normal['witnesses_matching_normal_form']+=fits
   if fits:gap_counts[C]+=1
 data['normal_form']=dict(normal);data['normal_form_door_gaps']=dict(gap_counts)
 (here/'swallow-shape.json').write_text(json.dumps(data,indent=2)+'\n')
 lines=['# Shape of whole-odd-part preservation','',f'Exact census through {X:,}. This is the SAME cohort as the full-power run: consecutive prime doors with disjoint odd supports, with a repeated odd factor in the preceding door, and at least one arriving prime preserving its entire odd part.','',
 'Write the preceding door as 2^u A with A odd. For EACH arriving prime r satisfying A | m0(r), decompose m0(r)/A uniquely as 2^k B, where B is odd. The proposed pure shape is B=1. If B>1, the door preserves A and carries additional odd multiplicity; those factors may repeat factors already in A, so they need not be new prime species. Every k is at least 1.','',
 '## Transition and witness counts','', '| Measure | Count |','|---|---:|']
 for key,n in counts.items():lines.append(f'| {key} | {n:,} |')
 lines+=['',f'{counts["pure_transitions"]/counts["transitions"]:.2%} of preserving transitions have at least one pure witness. {counts["pure_witnesses"]/counts["witnesses"]:.2%} of all witnesses are pure.','',
 '## Pure-shape powers of two','', '| k in m0(r)=2^k A | Witnesses | Share of pure witnesses |','|---:|---:|---:|']
 for k,n in sorted(pureks.items()):lines.append(f'| {k} | {n:,} | {n/counts["pure_witnesses"]:.2%} |')
 lines+=['','## Odd multipliers','', '| B in m0(r)=2^k A B | Witnesses |','|---:|---:|']
 for B,n in bs.most_common():lines.append(f'| {B} | {n:,} |')
 lines+=['','## First examples with an extra odd multiplier','', '| Consecutive primes | Old odd block A | Arriving r | m0(r) | k | B |','|---|---:|---:|---:|---:|---:|']
 examples=[(e,w) for e in events for w in e['witnesses'] if not w['pure']]
 for e,w in examples[:15]:lines.append(f'| {e["previous_prime"]} → {e["prime"]} | {e["A"]} | {w["r"]} | {w["door"]} | {w["k"]} | {w["B"]} |')
 lines+=['','## Interpretation and checks','',
 'This classifies selected successful whole-block preservations; it is not the prevalence of the shape among all transitions. It does not compare against a matched baseline or establish an adjacency effect. The other whole-odd-part preservations with squarefree preceding odd block are deliberately excluded to retain the original 1,336-event denominator.','',
 'Each quotient is checked exactly. Transition categories partition the cohort, and witness multiplicities reconstruct the witness count. The 10-million run asserts agreement with the previous 1,336 result. JSON contains every event and every preserving prime, including multiplicities and extra odd factors.','',
 'Run: python3 swallow_shape.py --limit 10000000 (keep waits.py, ingredient_transitions.py and the prior power-continuity.json beside it).','']
 lines += ['','## Stronger observed normal form','',f"{normal['witnesses_matching_normal_form']:,} of {counts['witnesses']:,} witnesses also satisfy: old door = 2^(v+k) A; next door = 2^v(2^k A+1); arriving prime r = 2^k A+1, with k,v >= 1 and r congruent to 2 modulo 3. The door gap is therefore exactly 2^v. This is an observed classification within this census, not an asserted universal theorem.",'', 'Normal-form door gaps (gap: witness count): '+str(dict(sorted(gap_counts.items())))+'.','', 'Independent verification of every listed transition and witness: python3 check_swallow_shape.py.','']
 (here/'swallow-shape.md').write_text('\n'.join(lines))
 print(json.dumps({k:v for k,v in data.items() if k!='events'},indent=2))
if __name__=='__main__':main()
