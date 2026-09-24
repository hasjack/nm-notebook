#!/usr/bin/env python3
"""Exact-stratum comparison of consecutive and nonconsecutive prime doors.
Standard library. Run beside waits.py and ingredient_transitions.py.
"""
from waits import sieve
from ingredient_transitions import fac
from collections import defaultdict,Counter
from functools import lru_cache
from pathlib import Path
import argparse,json,time

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--limit',type=int,default=10000000);X=ap.parse_args().limit
    start=time.perf_counter();spf=sieve(X+1)
    @lru_cache(maxsize=200000)
    def ingredients(p):return tuple(q for q in fac(p+(1 if p%3==1 else -1),spf) if q!=2)
    records=[]
    for p in range(5,X+1,2):
        if spf[p]:continue
        d=p+(1 if p%3==1 else -1);odd=ingredients(p);children=set()
        for q in odd:children.update(ingredients(q))
        largest=max(odd,default=1)
        profile=(len(odd),5 in odd,7 in odd,largest*largest>d)
        records.append((p,d,frozenset(odd),frozenset(children),profile))
    ingredients.cache_clear()
    # Gap is exact. Location is a dyadic band (all values within factor two).
    # Full profiles match odd-factor count, presence of 5 and 7, and whether
    # the largest factor exceeds sqrt(door). Coarse strata omit profiles.
    def keys(a,b):
        gap=b[1]-a[1];band=b[1].bit_length()-1
        coarse=(gap,band)
        return coarse,coarse+a[4]+b[4]
    obs=[defaultdict(lambda:[0,0]),defaultdict(lambda:[0,0])]
    ctl=[defaultdict(lambda:[0,0]),defaultdict(lambda:[0,0])]
    gapcounts=defaultdict(lambda:[0,0]);total=linked=0
    for a,b in zip(records,records[1:]):
        if a[2]&b[2]:continue
        outcome=bool(a[2]&b[3]);total+=1;linked+=outcome
        gap=b[1]-a[1];gapcounts[gap][0]+=1;gapcounts[gap][1]+=outcome
        for level,key in enumerate(keys(a,b)):
            c=obs[level][key];c[0]+=1;c[1]+=outcome
    maxgap=max(gapcounts);candidate_pairs=0
    for i,a in enumerate(records):
        j=i+2
        while j<len(records):
            b=records[j];gap=b[1]-a[1]
            if gap>maxgap:break
            j+=1
            if gap not in gapcounts or a[2]&b[2]:continue
            candidate_pairs+=1;ks=keys(a,b)
            if not any(key in obs[level] for level,key in enumerate(ks)):continue
            outcome=bool(a[2]&b[3])
            for level,key in enumerate(ks):
                if key in obs[level]:
                    c=ctl[level][key];c[0]+=1;c[1]+=outcome
    summaries=[]
    for level,label in enumerate(('Exact gap + location','Exact gap + location + both ingredient profiles')):
        for minimum in (1,10,30):
            n=hits=controls=chits=0;expected=0.;bygap=defaultdict(lambda:[0,0,0.])
            for key,(on,oh) in obs[level].items():
                cn,cc=ctl[level].get(key,(0,0))
                if cn<minimum:continue
                n+=on;hits+=oh;controls+=cn;chits+=cc;expected+=on*cc/cn
                c=bygap[key[0]];c[0]+=on;c[1]+=oh;c[2]+=on*cc/cn
            summaries.append(dict(level=label,min_controls_per_stratum=minimum,matched_observed=n,coverage=n/total,observed_linked=hits,observed_rate=hits/n if n else None,standardized_control_rate=expected/n if n else None,difference_percentage_points=100*(hits-expected)/n if n else None,controls=controls,raw_control_rate=chits/controls if controls else None,by_gap={g:dict(observed=v[0],linked=v[1],expected_links=v[2]) for g,v in sorted(bygap.items())}))
    data=dict(limit=X,seconds=time.perf_counter()-start,total_disjoint=total,total_linked=linked,max_observed_gap=maxgap,eligible_nonconsecutive_pairs=candidate_pairs,summaries=summaries,gap_observed=dict(gapcounts))
    here=Path(__file__).resolve().parent;(here/'matched-continuity.json').write_text(json.dumps(data,indent=2)+'\n')
    lines=['# Matched one-level continuity comparison','',f'Exact sieve through {X:,}. Observed population: {total:,} consecutive prime pairs with disjoint odd door support; {linked:,} reconnect one level deeper.','',
    'Outcome: an odd factor of the earlier door divides the door of an odd factor of the later door. Under disjoint immediate support, all later factors are arriving and all earlier ones departing. Multiplicity is ignored.','',
    'Controls are real nonconsecutive prime pairs, not synthetic ingredient swaps. They also have disjoint odd support. Their exact door gap must appear in the observed population. Location is the dyadic band of the later door: [2^b, 2^(b+1)). Full matching additionally uses, separately for each door: exact count of distinct odd factors; presence of 5; presence of 7; and whether its largest odd factor exceeds its square root.','',
    'Within each stratum, compute the control outcome rate. Weight that rate by the number of observed pairs in the same stratum. Compare with the observed rate on those same supported strata. Thus the displayed control rate is standardized to the matched observed distribution, not the raw pooled control average. Rows requiring 10 or 30 controls are sensitivity checks for sparse strata.','',
    '| Matching | Minimum controls per stratum | Matched neighbours | Coverage | Observed continuity | Standardized control | Difference (percentage points) |','|---|---:|---:|---:|---:|---:|---:|']
    for s in summaries:lines.append(f"| {s['level']} | {s['min_controls_per_stratum']} | {s['matched_observed']:,} | {s['coverage']:.2%} | {format(s['observed_rate'], '.2%') if s['observed_rate'] is not None else '—'} | {format(s['standardized_control_rate'], '.2%') if s['standardized_control_rate'] is not None else '—'} | {format(s['difference_percentage_points'], '+.3f') if s['difference_percentage_points'] is not None else '—'} |")
    lines+=['','## Coverage and interpretation','',
    'Door gaps 2 and 4 cannot have nonconsecutive prime controls: they correspond respectively to prime gaps 4 and 2 in these residue classes, with no intervening prime possible. Other strata can also lack controls. Results therefore concern the matched subset, not the complete 18.40% population.','',
    'This is an observational comparison. Consecutiveness encodes absence of intermediate primes; matching these summaries does not remove all arithmetic differences. Prime pairs share endpoints, controls are reused across sensitivity rows, and no independent-sample significance claim is made. A residual difference is not a causal adjacency effect. The profile definition was chosen before inspecting this run. The three minimum-count rows are sensitivity checks, not independent replications.','',
    'Full per-gap weighted counts are in JSON. Reproduce: python3 matched_continuity.py --limit 10000000 (requires bundled waits.py and ingredient_transitions.py). Run check_matched_continuity.py for independent small-window validation.','']
    (here/'matched-continuity.md').write_text('\n'.join(lines));print('\n'.join(lines[:16]));print('seconds',data['seconds'])
if __name__=='__main__':main()
