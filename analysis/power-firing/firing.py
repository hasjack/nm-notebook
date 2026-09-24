#!/usr/bin/env python3
"""Prime-power door firing census. python3 firing.py --limit 10000000
Standard library only; keep waits.py beside this file.
"""
from waits import sieve, summarize
from collections import Counter
from array import array
from pathlib import Path
from math import isqrt, prod
import argparse, json, csv, time

BASES=(5,7,11,13,17,19)
def factors(n,spf):
    out={}
    while n>1:
        q=spf[n] or n
        e=0
        while n%q==0:
            n//=q; e+=1
        out[q]=e
    return out

def stat(candidates, hits):
    positions={p:i for i,p in enumerate(candidates)}
    indices=[positions[p] for p in hits]
    gaps=[b-a for a,b in zip(hits,hits[1:])]
    misses=[b-a-1 for a,b in zip(indices,indices[1:])]
    def compact(xs):
        s=summarize(xs)
        if s: s.pop('histogram')
        return s
    return dict(opportunities=len(candidates),hits=len(hits),success_rate=len(hits)/len(candidates) if candidates else None,
                first_prime=hits[0] if hits else None,first_preceding_misses=indices[0] if indices else None,
                number_line_gaps=compact(gaps),missed_opportunities=compact(misses),
                trailing_misses=len(candidates)-indices[-1]-1 if indices else len(candidates),
                no_hit_is_censored=not bool(hits))

def main():
    parser=argparse.ArgumentParser(); parser.add_argument('--limit',type=int,default=10_000_000)
    limit=parser.parse_args().limit
    assert limit>=10000
    start=time.perf_counter(); spf=sieve(limit+1)
    records={}; exact={}; companions={}; structures={}
    for q in BASES:
        e=1
        while 2*q**e-1<=limit:
            key=(q,e); records[key]=array('I');exact[key]=array('I');companions[key]=Counter();structures[key]=Counter();e+=1
    total=0
    for p in range(5,limit+1,2):
        if spf[p]:continue
        total+=1
        d=p+(1 if p%3==1 else -1)
        fs=factors(d,spf)
        assert prod(q**e for q,e in fs.items())==d and 3 not in fs and 2 in fs
        for q in BASES:
            v=fs.get(q,0)
            if v:
                exact[q,v].append(p)
                for e in range(1,v+1):
                    key=(q,e);records[key].append(p)
                    companions[key].update(r for r in fs if r not in (2,q))
                    structures[key][len(fs)-2]+=1
    rows=[]
    for (q,e),hits in records.items():
        Q=q**e;s=1 if Q%3==1 else -1
        candidates=array('I'); exact_candidates=array('I')
        for t in range(limit//(6*Q)+1):
            for r in (2*Q-s,4*Q+s):
                n=6*Q*t+r
                if n>limit:continue
                d=n+(1 if n%3==1 else -1)
                assert d%Q==0
                candidates.append(n)
                if d%(Q*q):exact_candidates.append(n)
        assert len(hits)==len(exact[q,e])+len(records.get((q,e+1),[]))
        cumulative=stat(candidates,hits);ex=stat(exact_candidates,exact[q,e])
        assert len(hits)==sum(structures[q,e].values())
        first=hits[0] if hits else None
        rows.append(dict(q=q,exponent=e,power=Q,cumulative=cumulative,exact=ex,
             share_of_all_primes=len(hits)/total,
             next_power_share=len(records.get((q,e+1),[]))/len(hits) if hits else None,
             first_door_factors=factors(first+(1 if first%3==1 else -1),spf) if first else None,
             other_distinct_odd_factor_counts=dict(structures[q,e]),
             companions=[dict(prime=r,count=c,share=c/len(hits)) for r,c in companions[q,e].most_common(10)]))
    # Independent trial-division cross-check of primality, factorisation and
    # cumulative/exact membership throughout the first 10,000 integers.
    expected={k:[] for k in records}; expected_exact={k:[] for k in records}
    for p in range(5,10001,2):
        if any(p%d==0 for d in range(2,isqrt(p)+1)):continue
        door=p+(1 if p%3==1 else -1)
        for q in BASES:
            d=door;e=0
            while d%q==0:d//=q;e+=1
            if e:expected_exact[q,e].append(p)
            for a in range(1,e+1):expected[q,a].append(p)
    for k in records:
        assert expected[k]==[p for p in records[k] if p<=10000]
        assert expected_exact[k]==[p for p in exact[k] if p<=10000]
    data=dict(limit=limit,total_primes_gt3=total,bases=BASES,rows=rows,
              verification='Independent trial division through 10000; full-window nested-count and door-factorisation checks.',seconds=time.perf_counter()-start)
    here=Path(__file__).resolve().parent
    (here/'firing-results.json').write_text(json.dumps(data,indent=2)+'\n')
    with (here/'firing-table.csv').open('w') as f:
        fields=['q','exponent','power','first_prime','first_preceding_misses','opportunities','hits','success_percent','exact_hits','exact_opportunities','exact_success_percent','next_power_percent','mean_gap','mean_misses','max_misses']
        writer=csv.DictWriter(f,fieldnames=fields);writer.writeheader()
        for r in rows:
            c=r['cumulative'];x=r['exact'];m=c['missed_opportunities'];g=c['number_line_gaps']
            writer.writerow(dict(q=r['q'],exponent=r['exponent'],power=r['power'],first_prime=c['first_prime'],first_preceding_misses=c['first_preceding_misses'],opportunities=c['opportunities'],hits=c['hits'],success_percent=100*c['success_rate'] if c['success_rate'] is not None else None,exact_hits=x['hits'],exact_opportunities=x['opportunities'],exact_success_percent=100*x['success_rate'] if x['success_rate'] is not None else None,next_power_percent=100*r['next_power_share'] if r['next_power_share'] is not None else None,mean_gap=g['mean'] if g else None,mean_misses=m['mean'] if m else None,max_misses=m['maximum'] if m else None))
    lines=['# Prime-power firing census','',f'Exact sieve: primes 3 < p <= {limit:,}. {total:,} primes; bases {BASES}. All powers with 2q^e-1 <= X included, including lanes with no hits.','',
      'A cumulative firing means q^e divides m0(p). An exact firing means q^e divides it and q^(e+1) does not. Eligible positions use the two residues 2Q-chi3(Q), 4Q+chi3(Q) modulo 6Q. Exact-power opportunities also exclude positions divisible by the next power in their door. Percentages are prime hits divided by eligible positions, not by all integers.','',
      'Waits include only consecutive hits inside the window. Initial misses are separate; trailing runs and missing first appearances are censored. A zero-hit lane does not mean it never fires. Sparse high powers cannot support stable rate estimates. Lanes overlap; their counts are not independent.','',
      '| Ingredient | First prime | Prior misses | Hits | Exact hits | Eligible positions | Success | Mean number-line gap | Mean missed positions |','|---|---:|---:|---:|---:|---:|---:|---:|---:|']
    for r in rows:
        c=r['cumulative'];m=c['missed_opportunities'];g=c['number_line_gaps']
        lines.append(f"| {r['q']}^{r['exponent']} = {r['power']:,} | {c['first_prime'] or 'not seen'} | {c['first_preceding_misses'] if c['first_prime'] else '—'} | {c['hits']:,} | {r['exact']['hits']:,} | {c['opportunities']:,} | {100*c['success_rate']:.2f}% | {format(g['mean'], ',.2f') if g else '—'} | {format(m['mean'], '.3f') if m else '—'} |" if c['opportunities'] else f"| {r['q']}^{r['exponent']} | not seen | — | 0 | 0 | 0 | — | — | — |")
    lines+=['','## Companions','', 'Counts below are for cumulative lanes. Other odd primes exclude the lane base and the universal factor 2. A door may contribute to multiple companion counts.','', '| Lane | Top three other odd companions (share of hires) | No other odd prime |','|---|---|---:|']
    for r in rows:
        if r['exponent']>3:continue
        top='; '.join(f"{t['prime']}: {t['count']:,} ({t['share']:.2%})" for t in r['companions'][:3])
        lines.append(f"| {r['q']}^{r['exponent']} | {top} | {r['other_distinct_odd_factor_counts'].get(0,0):,} |")
    lines+=['','## Interpretation','', 'Compare powers within the same base using success per eligible position as well as raw number-line gaps. Higher powers thin the opportunity lattice. For example, progression counts suggest a q-fold reduction in opportunities for each extra power; the measured next-power share is provided in the data. This finite census does not establish an asymptotic theorem or independence.','', 'The next-power share uses cumulative hits as its denominator; exact shares are its complement. Companion percentages also use cumulative hits. The CSV gives all lanes; JSON additionally includes gap quantiles, censored boundaries, exact-lane waits, first-door factorisations and companion counts.','',data['verification'],'', 'Reproduce with Python 3: `python3 firing.py --limit 10000000` (keep waits.py alongside). No third-party dependencies, PRP tests, or network needed.','']
    (here/'firing-report.md').write_text('\n'.join(lines))
    print(json.dumps(dict(seconds=data['seconds'],total=total,lanes=len(rows))))
    for r in rows:
        if r['q']==7:print(json.dumps(r))
if __name__=='__main__':main()
