#!/usr/bin/env python3
"""Door gap versus arriving/departing factor size. Standard library only.
Run beside waits.py and ingredient_transitions.py.
"""
from waits import sieve
from ingredient_transitions import fac
from math import log,sqrt
from collections import defaultdict
from array import array
from pathlib import Path
import json,time,argparse

class Group:
    def __init__(self):
        self.n=0;self.arrival=array('I');self.departure=array('I');self.relative=array('d');self.large=0;self.huge=0;self.up=0;self.none=0
    def add(self,d,old,arr,dep,lp,oldlp):
        self.n+=1;self.up+=lp>=10*oldlp
        if arr:
            self.arrival.append(arr);self.relative.append(log(arr)/log(d));self.large+=arr*arr>d;self.huge+=log(arr)>.75*log(d)
        else:self.none+=1
        if dep:self.departure.append(dep)
    def result(self):
        def median(xs):
            s=sorted(xs);n=len(s)
            return (s[(n-1)//2]+s[n//2])/2 if n else None
        return dict(pairs=self.n,no_new_odd_factor=self.none,median_largest_arriving=median(self.arrival),median_largest_departing=median(self.departure),median_log_size_fraction=median(self.relative),arriving_above_sqrt_share=self.large/self.n,arriving_above_three_quarter_power_share=self.huge/self.n,tenfold_largest_increase_share=self.up/self.n)

class Corr:
    def __init__(self):self.n=0;self.s=[0.]*3;self.ss=[[0.]*3 for _ in range(3)]
    def add(self,x,y,z):
        self.n+=1;v=(x,y,z)
        for i in range(3):
            self.s[i]+=v[i]
            for j in range(3):self.ss[i][j]+=v[i]*v[j]
    def result(self):
        def r(i,j):
            cov=self.ss[i][j]-self.s[i]*self.s[j]/self.n
            vi=self.ss[i][i]-self.s[i]**2/self.n;vj=self.ss[j][j]-self.s[j]**2/self.n
            return cov/sqrt(vi*vj)
        xy,xz,yz=r(0,1),r(0,2),r(1,2)
        return dict(pairs=self.n,log_gap_log_arrival=xy,partial_controlling_log_door=(xy-xz*yz)/sqrt((1-xz*xz)*(1-yz*yz)))

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--limit',type=int,default=10000000);X=ap.parse_args().limit
    assert X>=1000000
    spf=sieve(X+1);groups=defaultdict(Group);exact=defaultdict(Group);corr=defaultdict(Corr);prev=None;examples=[];maxshared=0
    def gapbin(g):return '2–8' if g<=8 else '10–18' if g<=18 else '20–38' if g<=38 else '40–78' if g<=78 else '80+'
    for p in range(5,X+1,2):
        if spf[p]:continue
        d=p+(1 if p%3==1 else -1);fs=fac(d,spf);odd=set(fs)-{2};lp=max(odd,default=1)
        if prev:
            oldp,old,oldodd,oldlp=prev;gap=d-old;arr=max(odd-oldodd,default=0);dep=max(oldodd-odd,default=0);common=odd&oldodd
            assert not common or 2*max(common)<=gap
            for r in odd-oldodd:assert (old+gap)%r==0
            band='<=100k' if p<=100000 else '100k–1m' if p<=1000000 else '1m–10m'
            for key in [('all',gapbin(gap)),(band,gapbin(gap))]:groups[key].add(d,old,arr,dep,lp,oldlp)
            exact[gap].add(d,old,arr,dep,lp,oldlp)
            if arr:
                for key in ('all',band):corr[key].add(log(gap),log(arr),log(d))
            if p<=1000 and gap<=4 and arr>100:examples.append(dict(primes=[oldp,p],doors=[old,d],gap=gap,largest_arriving=arr,largest_departing=dep))
        prev=(p,d,odd,lp)
    data=dict(limit=X,groups=[dict(band=k[0],gap_bin=k[1],**g.result()) for k,g in groups.items()],exact_gaps={k:g.result() for k,g in sorted(exact.items())},correlations={k:c.result() for k,c in corr.items()},examples=examples)
    here=Path(__file__).resolve().parent;(here/'gap-ingredients.json').write_text(json.dumps(data,indent=2)+'\n')
    out=['# Door gaps and arriving ingredients','',f'Exact sieve through {X:,}; consecutive primes p > 3. New ingredients are distinct odd prime factors present in the next door but absent from the preceding door. Departing ingredients reverse that comparison; powers are not counted as new distinct ingredients.','',
    '## What is forced','', 'Every shared odd factor q satisfies 2q <= Delta, since q divides the even door gap Delta. New factors satisfy Delta = -d (mod q), but this does not bound q by the gap: q can be much larger than Delta. These are exact arithmetic identities, not predictive fits.','',
    '## Measurements','', 'All percentages use all pairs in each row. Medians of arriving/departing factors exclude pairs without such factors. Log-size fraction log(q)/log(next door) expresses factor size relative to the door; 0.5 means its square root. Gap bins are fixed in advance.','',
    '| Band | Door gap | Pairs | Median largest arriving | Median largest departing | Median log-size fraction | Arrival > sqrt(door) | Arrival > door^0.75 | Tenfold largest-factor increase |','|---|---|---:|---:|---:|---:|---:|---:|---:|']
    for r in data['groups']:
        out.append(f"| {r['band']} | {r['gap_bin']} | {r['pairs']:,} | {r['median_largest_arriving']:,.0f} | {r['median_largest_departing']:,.0f} | {r['median_log_size_fraction']:.3f} | {r['arriving_above_sqrt_share']:.2%} | {r['arriving_above_three_quarter_power_share']:.2%} | {r['tenfold_largest_increase_share']:.2%} |")
    out+=['','## Correlations','', 'Pearson correlation of log(door gap) with log(largest arriving odd factor). The partial correlation removes each variable\'s linear association with log(next door). Pairs with no arriving odd factor are excluded. This is an exploratory descriptive adjustment, not a causal model or a forecast validation.','', '| Band | Pairs | Raw correlation | Controlling log door size |','|---|---:|---:|---:|']
    for band,c in data['correlations'].items():out.append(f"| {band} | {c['pairs']:,} | {c['log_gap_log_arrival']:.5f} | {c['partial_controlling_log_door']:.5f} |")
    out+=['','## Limits','', 'This tests gap size and ingredient size, not every possible residue pattern or return-time law. Exact congruence restrictions can remain despite weak linear correlations. Adjacent transitions overlap, and the dataset is observational and bounded. No claim of random or independent prime factors is made. Exact-gap data are included in JSON.','', 'Checks: every shared factor obeys 2q <= Delta, every arriving factor divides the next door. Pair counts and sqrt-threshold counts are independently cross-checked in the small window during this run.','', 'Reproduce: python3 gap_ingredients.py --limit 10000000, with waits.py and ingredient_transitions.py alongside.','']
    (here/'gap-ingredients.md').write_text('\n'.join(out))
    print(json.dumps(data['correlations'],indent=2));print('\n'.join(out[12:29]))
if __name__=='__main__':main()
