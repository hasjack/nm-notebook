#!/usr/bin/env python3
"""Full prime-power and whole odd-part continuity, exact census and matching."""
from waits import sieve
from ingredient_transitions import fac
from collections import Counter,defaultdict
from functools import lru_cache
from pathlib import Path
from math import prod
import json,argparse,time

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--limit',type=int,default=10000000);X=ap.parse_args().limit
    spf=sieve(X+1);start=time.perf_counter()
    @lru_cache(maxsize=200000)
    def fs(p):return tuple((q,e) for q,e in fac(p+(1 if p%3==1 else -1),spf).items() if q!=2)
    rows=[]
    for p in range(5,X+1,2):
        if spf[p]:continue
        d=p+(1 if p%3==1 else -1);f=fs(p);odd=frozenset(q for q,e in f)
        child=tuple((q,q+(1 if q%3==1 else -1)) for q,e in f)
        rep=tuple((q,e) for q,e in f if e>=2)
        profile=(len(f),dict(f).get(5,0),dict(f).get(7,0),max(odd,default=1)**2>d,len(rep),max((e for q,e in f),default=0))
        rows.append((p,d,f,odd,child,rep,profile,prod(q**e for q,e in f)))
    fs.cache_clear()
    def outcome(a,b):
        # Restrict to the repeated departing factors. Full means at least the
        # original exponent is retained in one arriving prime's own door.
        linked=full=False
        for q,e in a[5]:
            linked |= any(cd%q==0 for r,cd in b[4])
            full |= any(cd%(q**e)==0 for r,cd in b[4])
        whole=a[7]>1 and any(cd%a[7]==0 for r,cd in b[4])
        return int(linked),int(full),int(whole)
    def key(a,b):return (b[1]-a[1],b[1].bit_length()-1)+a[6]+b[6]
    obs=defaultdict(lambda:[0,0,0,0]);ctl=defaultdict(lambda:[0,0,0,0]);counts=Counter();exponents=defaultdict(Counter);examples=[];small=Counter()
    for a,b in zip(rows,rows[1:]):
        if a[3]&b[3]:continue
        counts['disjoint']+=1
        linked,full,whole=outcome(a,b)
        counts['whole_odd_part_preserved_all']+=whole
        if a[7]>1:counts['nonempty_old_odd_part']+=1
        if not a[5]:continue
        counts['repeated_factor_opportunities']+=1
        counts['repeated_factor_reconnects']+=linked
        counts['full_power_preserved']+=full
        counts['whole_odd_part_preserved_repeated']+=whole
        values=(1,linked,full,whole)
        cell=obs[key(a,b)]
        for i,v in enumerate(values):cell[i]+=v
        if b[0]<=10000:
            for k,v in zip(('opportunities','linked','full','whole'),values):small[k]+=v
        for q,e in a[5]:
            c=exponents[e];c['opportunities']+=1
            c['linked']+=any(cd%q==0 for r,cd in b[4])
            c['full']+=any(cd%(q**e)==0 for r,cd in b[4])
        if full and b[0]<=10000:
            paths=[dict(arriving=r,departing=q,power=e,child_door=cd) for q,e in a[5] for r,cd in b[4] if cd%(q**e)==0]
            examples.append(dict(previous_prime=a[0],prime=b[0],previous_door=a[1],door=b[1],old_factorisation=a[2],new_factorisation=b[2],paths=paths,whole_odd_part=bool(whole)))
        if a[0]==499 and b[0]==503:assert full and whole
    maxgap=max(k[0] for k in obs)
    for i,a in enumerate(rows):
        if not a[5]:continue
        j=i+2
        while j<len(rows):
            b=rows[j];j+=1
            if b[1]-a[1]>maxgap:break
            k=key(a,b)
            if k not in obs or a[3]&b[3]:continue
            values=(1,)+outcome(a,b);cell=ctl[k]
            for index,v in enumerate(values):cell[index]+=v
    matched=[]
    for minimum in (1,10,30):
        n=nc=0;hits=[0,0,0];expected=[0.,0.,0.]
        for k,o in obs.items():
            c=ctl.get(k,(0,0,0,0))
            if c[0]<minimum:continue
            n+=o[0];nc+=c[0]
            for i in range(3):hits[i]+=o[i+1];expected[i]+=o[0]*c[i+1]/c[0]
        matched.append(dict(min_controls=minimum,observed_pairs=n,coverage=n/counts['repeated_factor_opportunities'],controls=nc,observed_hits=hits,expected_hits=expected,observed_rates=[v/n if n else None for v in hits],control_rates=[v/n if n else None for v in expected]))
    data=dict(limit=X,seconds=time.perf_counter()-start,counts=dict(counts),small_window=dict(small),by_departing_exponent={k:dict(v) for k,v in exponents.items()},matched=matched,examples=examples)
    here=Path(__file__).resolve().parent;(here/'power-continuity.json').write_text(json.dumps(data,indent=2)+'\n')
    c=counts
    lines=['# Preserving powers through an arriving prime','',f'Exact sieve of consecutive prime doors through {X:,}. Directly disjoint odd support is required throughout.','',
    'For a departing odd factor q appearing with exponent e >= 2 in the preceding door, test whether any arriving prime r satisfies q | m0(r), and whether any satisfies q^e | m0(r). Full preservation means at least the old exponent, not necessarily equality. Whole-odd-part preservation requires a SINGLE arriving prime whose door is divisible by the entire odd part of the old door. The vacuous odd part 1 is excluded.','',
    '## Counts','', '| Measure | Count |','|---|---:|']
    for k,v in c.items():lines.append(f'| {k} | {v:,} |')
    n=c['repeated_factor_opportunities'];linked=c['repeated_factor_reconnects'];full=c['full_power_preserved']
    lines+=['',f'Among {n:,} transitions with at least one repeated departing odd factor: {linked/n:.2%} reconnect through a repeated factor, {full/n:.2%} preserve at least one full power, and {c["whole_odd_part_preserved_repeated"]/n:.2%} preserve the entire old odd part through a single arriving prime. Among the {linked:,} repeated-factor reconnections, {full/linked:.2%} preserve a full power. These are pair-level counts; multiple successes in one pair count once.','',
    '## By exponent','', 'This table counts (transition, departing repeated prime) opportunities; rows can overlap at transition level.','', '| Departing exponent | Opportunities | Reconnect through prime | Preserve full power | Full among reconnected |','|---:|---:|---:|---:|---:|']
    for e,c in sorted(exponents.items()):lines.append(f'| {e} | {c["opportunities"]:,} | {c["linked"]:,} | {c["full"]:,} | {c["full"]/c["linked"]:.2%} |' if c['linked'] else f'| {e} | {c["opportunities"]:,} | 0 | 0 | — |')
    lines+=['','## Matched comparison','',
    'Controls: real nonconsecutive prime pairs, also with disjoint odd support and repeated departing factors. Match exact door gap, dyadic location band of the later door, and both doors\' profiles: distinct odd-factor count, EXACT exponents of 5 and 7, whether the largest factor exceeds sqrt(door), number of repeated odd factors, and maximum odd exponent. Control rates within each stratum are weighted by observed pair counts. These profiles are stricter than the previous support-only census.','',
    '| Minimum controls | Matched observed pairs | Coverage | Full-power observed | Full-power controls | Whole odd part observed | Whole odd part controls |','|---:|---:|---:|---:|---:|---:|---:|']
    def pct(x):return f'{x:.2%}' if x is not None else '—'
    for m in matched:lines.append(f'| {m["min_controls"]} | {m["observed_pairs"]:,} | {m["coverage"]:.2%} | {pct(m["observed_rates"][1])} | {pct(m["control_rates"][1])} | {pct(m["observed_rates"][2])} | {pct(m["control_rates"][2])} |')
    lines+=['','## Examples','', '| Consecutive primes | Doors | Full-power paths | Entire odd part? |','|---|---|---|---|']
    for e in examples[:30]:lines.append(f'| {e["previous_prime"]} → {e["prime"]} | {e["previous_door"]} → {e["door"]} | '+ '; '.join(f'{t["arriving"]}: {t["departing"]}^{t["power"]} divides {t["child_door"]}' for t in e['paths'])+f' | {e["whole_odd_part"]} |')
    lines+=['','## Limits','',
    'Door gaps 2 and 4 have no nonconsecutive prime controls. This includes 499 → 503. Matching therefore cannot assess adjacency enhancement for that example; sparse profiles further reduce coverage. Matched rates refer to their own subsets, not the complete census. Paired records share endpoints; these are descriptive comparisons, not independent significance tests or causal estimates. Exact identities can force some examples: if old door=4A, next door=4A+2 and r=2A+1 is an arriving prime with m0(r)=2A, it preserves all of A. Such constructions do not establish a general law of inheritance.','',
    'Reproduce: python3 power_continuity.py --limit 10000000 (with waits.py and ingredient_transitions.py). Independent trial-division validation: python3 check_power_continuity.py.','']
    (here/'power-continuity.md').write_text('\n'.join(lines));print(json.dumps({k:data[k] for k in ['counts','by_departing_exponent','matched']},indent=2))
if __name__=='__main__':main()
