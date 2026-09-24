#!/usr/bin/env python3
"""One-level ingredient links. Run beside waits.py and ingredient_transitions.py."""
from waits import sieve
from ingredient_transitions import fac
from collections import Counter
from pathlib import Path
from functools import lru_cache
import argparse,json,time

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--limit',type=int,default=10000000);X=ap.parse_args().limit
    start=time.perf_counter();spf=sieve(X+1)
    @lru_cache(maxsize=200000)
    def odddoor(p):return tuple(q for q in fac(p+(1 if p%3==1 else -1),spf) if q!=2)
    counts=Counter();byprime=Counter();examples=[];rows=[];prev=None
    for p in range(5,X+1,2):
        if spf[p]:continue
        odd=odddoor(p)
        if prev:
            a,old=prev;oldset=set(old);current=set(odd);direct=bool(oldset&current)
            arriving=current-oldset;parents=set()
            for q in arriving:parents.update(odddoor(q))
            common=parents&oldset
            counts['pairs']+=1;counts['direct']+=direct;counts['deeper_any']+=bool(common)
            if not direct:
                counts['disjoint']+=1;counts['disjoint_with_deeper']+=bool(common)
                counts['disjoint_with_deeper_other_than_5']+=bool(common-{5})
                counts['disjoint_old_has_5']+=5 in oldset
                if 5 not in oldset:
                    counts['disjoint_old_without_5']+=1;counts['disjoint_old_without_5_deeper']+=bool(common)
                byprime.update(common)
                rows.append((old,odd,tuple(parents)))
                if common and p<=1000:
                    paths=[(q,list(set(odddoor(q))&oldset)) for q in arriving if set(odddoor(q))&oldset]
                    examples.append(dict(previous_prime=a,prime=p,old_factors=old,new_factors=odd,paths=paths))
            if a==499 and p==503:assert 5 in common and 251 in arriving
        prev=p,odd
    # Descriptive local re-pairing reference, not independent samples or a
    # significance test. Re-pair only the already disjoint transition records.
    # Keep target door and its children fixed; replace preceding-door ingredients
    # with those from another record in a block of 1000 disjoint transitions.
    # Retain only re-pairings with disjoint direct supports, as in the target set.
    baselines=[]
    for offset in (137,389,613):
        c=Counter()
        for start_i in range(0,len(rows),1000):
            block=rows[start_i:start_i+1000];n=len(block)
            if n<=1:continue
            shift=offset%n or 1
            for i,(_,dest,children) in enumerate(block):
                origin=set(block[(i+shift)%n][0])
                if origin.intersection(dest):continue
                common=origin.intersection(children)
                c['pairs']+=1;c['deeper']+=bool(common);c['other_than_5']+=bool(common-{5})
                if 5 not in origin:
                    c['origin_without_5']+=1;c['origin_without_5_deeper']+=bool(common)
        baselines.append(dict(offset=offset,**c))
    data=dict(limit=X,seconds=time.perf_counter()-start,counts=dict(counts),shared_ancestors=byprime.most_common(20),baselines=baselines,examples=examples)
    here=Path(__file__).resolve().parent;(here/'deeper-connections.json').write_text(json.dumps(data,indent=2)+'\n')
    c=counts
    lines=['# One level deeper: ingredient continuity','',f'Exact sieve through {X:,}; {c["pairs"]:,} consecutive prime transitions.','',
      'For a preceding prime a and next prime p, let O be the odd prime factors of m0(a), and N those of m0(p). Arriving factors are N minus O. Expand each arriving prime q to the odd prime factors of its own door m0(q). A deeper connection is an intersection of that union with O. Both 2 and 3 are excluded; multiplicities are ignored. This is exactly one additional edge, not eventual connectivity.','',
      '## Observed transitions','', '| Measure | Count |','|---|---:|']
    for k,v in c.items():lines.append(f'| {k} | {v:,} |')
    lines+=['',f'Of directly disjoint transitions, {c["disjoint_with_deeper"]/c["disjoint"]:.2%} reconnect one level deeper. {c["disjoint_with_deeper_other_than_5"]/c["disjoint"]:.2%} reconnect through at least one prime other than 5.', '',
      f'When the preceding door has no factor 5, {c["disjoint_old_without_5_deeper"]:,} of {c["disjoint_old_without_5"]:,} directly disjoint transitions reconnect ({c["disjoint_old_without_5_deeper"]/c["disjoint_old_without_5"]:.2%}).','',
      '## Local re-pairing comparison','', 'Partition the directly disjoint transition records, in increasing prime order, into blocks of 1000 records. Keep each destination door and its one-level expansion fixed. Cyclically shift the origin ingredient sets within each block by each specified offset; discard re-pairings that now share a direct ingredient. This preserves local ingredients approximately and enforces direct disjointness, but changes the original gap distribution and is not a matched causal experiment or significance test. The offsets give descriptive sensitivity checks, not independent trials.','',
      '| Offset | Retained re-pairings | Deeper connection | Via non-5 ingredient | Origin lacks 5: deeper connection |','|---:|---:|---:|---:|---:|']
    for b in baselines:lines.append(f'| {b["offset"]} | {b["pairs"]:,} | {b["deeper"]/b["pairs"]:.2%} | {b["other_than_5"]/b["pairs"]:.2%} | {b["origin_without_5_deeper"]/b["origin_without_5"]:.2%} |')
    lines+=['','## Shared ingredients at the deeper level','', 'Counts overlap when a transition reconnects through several ingredients.','', '| Ingredient | Disjoint transitions reconnecting through it |','|---:|---:|']
    for q,n in byprime.most_common(20):lines.append(f'| {q} | {n:,} |')
    lines+=['','## Examples','', '| Consecutive primes | Previous odd ingredients | Next odd ingredients | Next factor → previous ingredient |','|---|---|---|---|']
    for e in examples[:30]:lines.append(f'| {e["previous_prime"]} → {e["prime"]} | {e["old_factors"]} | {e["new_factors"]} | {e["paths"]} |')
    lines+=['','## Scope','', 'These results establish how often one-step hidden overlap occurs in this window. They do not by themselves establish that adjacent doors are specially linked, forecast the next prime, or preserve exact powers. The 499 → 503 example is asserted by the script. Run check_deeper_connections.py for an independent trial-division check of the first 10,000.','', 'Reproduce: python3 deeper_connections.py --limit 10000000. Requires the bundled waits.py and ingredient_transitions.py; standard library only.','']
    (here/'deeper-connections.md').write_text('\n'.join(lines));print(json.dumps(data,indent=2))
if __name__=='__main__':main()
