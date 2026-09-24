#!/usr/bin/env python3
"""Consecutive prime door ingredient changes. Python standard library only.
Run beside waits.py: python3 ingredient_transitions.py --limit 10000000
"""
from waits import sieve
from collections import Counter,defaultdict
from math import gcd,prod
from pathlib import Path
import argparse,json,time

def fac(n,spf):
    d={}
    while n>1:
        q=spf[n] or n;e=0
        while n%q==0:n//=q;e+=1
        d[q]=e
    return d

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--limit',type=int,default=10_000_000);X=ap.parse_args().limit
    start=time.perf_counter();spf=sieve(X+1)
    overall=Counter(); gaps=defaultdict(Counter); bands=defaultdict(Counter); signed=defaultdict(Counter)
    carries=Counter(); examples=[]; early=[];prev=None
    # Lagged odd-factor intersection, grouped by position separation among primes.
    lags=(1,2,3,4,5,10,20,50,100); lagstats=defaultdict(Counter);history=[]
    for p in range(5,X+1,2):
        if spf[p]:continue
        sign=1 if p%3==1 else -1;door=p+sign; fs=fac(door,spf);odd=set(fs)-{2};lp=max(odd,default=1)
        assert prod(q**e for q,e in fs.items())==door and 3 not in fs
        for lag in lags:
            if len(history)>=lag:
                old=history[-lag];lagstats[lag]['pairs']+=1
                lagstats[lag]['shared']+=bool(odd & old)
        history.append(odd)
        if len(history)>100:history.pop(0)
        if prev:
            a,ds,oldfs,oldodd,oldlp,olds=prev
            common=oldodd&odd; delta=door-ds; g=gcd(ds,door)
            assert g==gcd(ds,delta)
            assert all(delta%q==0 for q in common)
            # Remove all powers of 2 and 3 from gap: no other allowed shared
            # factors if the remainder is 1.
            rem=delta
            for q in (2,3):
                while rem%q==0:rem//=q
            forced=rem==1
            assert not forced or not common
            band=0 if p<=10000 else 10000 if p<=100000 else 100000 if p<=1000000 else 1000000
            targets=[overall,gaps[delta],bands[band],signed[f'{olds}->{sign}']]
            for c in targets:
                c['pairs']+=1;c['shared']+=bool(common);c['disjoint']+=not bool(common)
                c['forced_disjoint_by_gap']+=forced
                c['largest_same']+=lp==oldlp
                c['largest_up_10x']+=lp>=10*oldlp
                c['largest_down_10x']+=oldlp>=10*lp
                c['pure_two_endpoint']+=(lp==1 or oldlp==1)
                c['same_odd_support']+=odd==oldodd
            carries.update(common)
            item=dict(p=a,next_prime=p,door=ds,next_door=door,factors=oldfs,next_factors=fs,door_gap=delta,shared=sorted(common),largest_ratio=lp/oldlp)
            if p<=200:early.append(item)
            if p<=10000 and lp>=10*oldlp and oldlp>1:examples.append(item)
        prev=(p,door,fs,odd,lp,sign)
    data=dict(limit=X,seconds=time.perf_counter()-start,overall=dict(overall),door_gaps={k:dict(v) for k,v in sorted(gaps.items())},bands={k:dict(v) for k,v in sorted(bands.items())},sign_transitions={k:dict(v) for k,v in signed.items()},shared_primes=carries.most_common(20),lags={k:dict(v) for k,v in lagstats.items()},early=early,examples=examples[:15])
    assert overall['pairs']==lagstats[1]['pairs'] and overall['shared']==lagstats[1]['shared']
    here=Path(__file__).resolve().parent;(here/'ingredient-transitions.json').write_text(json.dumps(data,indent=2)+'\n')
    lines=['# Ingredient changes between consecutive prime doors','',f'Exact census through {X:,}; {overall["pairs"]:,} consecutive prime pairs, starting at 5.','',
    'For each prime p > 3, d = p + chi3(p). Shared ingredients count distinct odd prime factors: 2 is universal and excluded; powers are retained in the example factorisations. Largest odd factor is defined as 1 for a pure power-of-two door.','',
    '## Exact restriction','', 'For consecutive primes p < r, write d=m0(p), e=m0(r), Delta=e-d. Then gcd(d,e)=gcd(d,Delta). Every shared odd ingredient must therefore divide Delta. Since neither door contains 3, a gap Delta=2^a*3^b forces disjoint odd ingredients. This is true for all pairs, not just consecutive ones. Door gaps differ from prime gaps by chi3(r)-chi3(p).','',
    '## Census','', '| Measure | Count | Share of pairs |','|---|---:|---:|']
    for key in ['shared','disjoint','forced_disjoint_by_gap','largest_same','largest_up_10x','largest_down_10x','pure_two_endpoint','same_odd_support']:
        lines.append(f'| {key} | {overall[key]:,} | {overall[key]/overall["pairs"]:.2%} |')
    lines+=['','## By door gap','', '| Door gap | Pairs | Shared odd ingredients | Share |','|---:|---:|---:|---:|']
    for gap,c in sorted(gaps.items()):
        lines.append(f'| {gap} | {c["pairs"]:,} | {c["shared"]:,} | {c["shared"]/c["pairs"]:.2%} |')
    lines+=['','## By endpoint band','', '| Larger endpoint band | Pairs | Shared | Forced disjoint | Largest grows 10x |','|---|---:|---:|---:|---:|']
    for lo,c in sorted(bands.items()):
        hi={0:10000,10000:100000,100000:1000000,1000000:X}[lo]
        lines.append(f'| ({lo:,}, {hi:,}] | {c["pairs"]:,} | {c["shared"]/c["pairs"]:.2%} | {c["forced_disjoint_by_gap"]/c["pairs"]:.2%} | {c["largest_up_10x"]/c["pairs"]:.2%} |')
    lines+=['','## Separation in prime positions','', 'Descriptive overlap at fixed lag; not a significance test or a test of independence. Lag means number of steps in the prime sequence, not integer distance.','', '| Lag | Pairs | Share with common odd factor |','|---:|---:|---:|']
    for lag,c in lagstats.items():lines.append(f'| {lag} | {c["pairs"]:,} | {c["shared"]/c["pairs"]:.2%} |')
    lines+=['','## Abrupt changes below 10,000','', '| Consecutive primes | Door factorisations | Largest-factor multiplier |','|---|---|---:|']
    def fmt(fs):return ' · '.join(str(q)+(f'^{e}' if e>1 else '') for q,e in fs.items())
    for t in examples[:15]:lines.append(f'| {t["p"]} → {t["next_prime"]} | {fmt(t["factors"])} → {fmt(t["next_factors"])} | {t["largest_ratio"]:.2f} |')
    lines+=['','## Limits and checks','', 'All primality and factorisation results use an exact sieve. Every factorisation was reconstructed and every adjacent pair checked against the gcd identity. Totals were cross-checked against the lag-one computation. Long-window averages do not show a periodic prime pattern. Local modular exclusions are exact, while the counts of which permitted positions are prime remain empirical here. Categories overlap: forced-disjoint is a subset of disjoint, and largest-factor events may overlap other categories. Bands assign each pair by its larger endpoint.','', 'Reproduce: `python3 ingredient_transitions.py --limit 10000000`, with waits.py beside it.','']
    (here/'ingredient-transitions.md').write_text('\n'.join(lines))
    print(json.dumps({k:data[k] for k in ['overall','lags','examples']},indent=2))
if __name__=='__main__':main()
