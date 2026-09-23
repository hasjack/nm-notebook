#!/usr/bin/env python3
"""Exact candidate-lattice waits; standard library only.

python3 analysis/door-coverage/waits.py --limit 10000000
Writes waits-results.json and waits-report.md beside this file.
"""
import argparse
from array import array
from collections import Counter
from math import ceil, isqrt
from pathlib import Path
import json
import time

QS = (5, 7, 49, 11)
BOUND = 100


def sieve(limit):
    spf = array("I", [0]) * (limit + 1)
    for p in range(2, isqrt(limit) + 1):
        if spf[p] == 0:
            for n in range(p * p, limit + 1, p):
                if spf[n] == 0:
                    spf[n] = p
    return spf  # n>=2 is prime exactly when spf[n] is zero.


def summarize(values):
    if not values:
        return None
    counts = Counter(values)
    total = len(values)
    mean = sum(values) / total
    def quantile(p):
        target, accumulated = ceil(p * total), 0
        for x, n in sorted(counts.items()):
            accumulated += n
            if accumulated >= target:
                return x
    return dict(count=total, mean=mean, variance=sum((x-mean)**2 * n for x,n in counts.items())/total,
                median=quantile(.5), p90=quantile(.9), p99=quantile(.99), maximum=max(values),
                histogram={str(k):v for k,v in sorted(counts.items())})


def analyze(q, spf, lo, hi):
    s = 1 if q % 3 == 1 else -1
    residues = (2*q-s, 4*q+s)
    blocks, transition = Counter(), Counter()
    misses, filtered_misses, numeric_gaps = [], [], []
    count = hits = kept = 0
    classes = [{"candidates":0,"hits":0},{"candidates":0,"hits":0}]
    previous = None
    first = None
    longest = None
    candidate_index = -1
    survivor_index = -1
    survivor_classes = array('B')
    # Only complete intervals with both prime endpoints in this band enter
    # wait statistics. Boundary runs are reported separately as censored.
    for t in range(max(0, lo//(6*q)-1), hi//(6*q)+1):
        for c, residue in enumerate(residues):
            n = 6*q*t+residue
            if not lo < n <= hi:
                continue
            assert (n + (1 if n % 3 == 1 else -1)) % q == 0
            candidate_index += 1
            count += 1
            classes[c]["candidates"] += 1
            prime = spf[n] == 0
            survives = prime or spf[n] > BOUND
            if survives:
                survivor_index += 1
                kept += 1
                survivor_classes.append(c)
            if not prime:
                blocks[str(spf[n]) if spf[n] <= BOUND else ">100"] += 1
                continue
            hits += 1
            classes[c]["hits"] += 1
            current = (n, candidate_index, survivor_index, c)
            if first is None:
                first = current
            if previous is not None:
                gap = n-previous[0]
                m = candidate_index-previous[1]-1
                fm = survivor_index-previous[2]-1
                assert gap % (6*q) in (0, (2*q+2*s)%(6*q), (-2*q-2*s)%(6*q))
                assert (c != previous[3]) == (m % 2 == 0)
                misses.append(m)
                filtered_misses.append(fm)
                numeric_gaps.append(gap)
                transition[f"{previous[3]}->{c}"] += 1
                if longest is None or m > longest["misses"]:
                    longest = dict(start=previous[0], end=n, misses=m, survivingMisses=fm, numericGap=gap)
            previous = current
    assert count == hits+sum(blocks.values())
    assert kept == hits+blocks[">100"]
    assert sum(transition.values()) == max(0,hits-1)
    hazard = hits/count if count else 0
    filtered_hazard = hits/kept if kept else 0
    # Exact expectation for an independent Bernoulli labelling of the actual
    # <=100-sieve survivor sequence. This preserves all its class spacings.
    mass = [0.0, 0.0]  # Probabilities that the last successful class was 0/1.
    wheel_switch = wheel_same = 0.0
    for c in survivor_classes:
        wheel_switch += filtered_hazard * mass[1-c]
        wheel_same += filtered_hazard * mass[c]
        mass = [(1-filtered_hazard)*m for m in mass]
        mass[c] += filtered_hazard
    expected_edges = kept*filtered_hazard - 1 + (1-filtered_hazard)**kept if kept else 0
    assert abs(wheel_switch+wheel_same-expected_edges) < 1e-4
    return dict(q=q, lowerExclusive=lo, upperInclusive=hi, candidates=count, primeHits=hits,
                survivorCandidates=kept, successRate=hazard, survivorSuccessRate=filtered_hazard,
                classes=classes, smallestBlockers=dict(blocks), transitions=dict(transition),
                candidateMisses=summarize(misses), survivorMisses=summarize(filtered_misses),
                numericGaps=summarize(numeric_gaps), longest=longest,
                boundary=dict(firstPrime=first[0] if first else None,
                              leadingMisses=first[1] if first else count,
                              trailingMisses=candidate_index-previous[1] if previous else count,
                              trailingIsCensored=True,leadingIsFirstHire=(lo==0)),
                independentBaseline=dict(
                    note="Geometric comparison fitted to this band's overall success rate; not a theorem or significance test.",
                    meanMisses=(1-hazard)/hazard if hazard else None,
                    switchFraction=1/(2-hazard) if hazard else None,
                    zeroMissFraction=hazard,
                    filteredZeroMissFraction=filtered_hazard),
                sieveAwareBaseline=dict(
                    note="Independent constant-rate prime labels on the actual <=100-sieve survivor sequence; fitted within this band.",
                    switchFraction=wheel_switch/(wheel_switch+wheel_same) if wheel_switch+wheel_same else None,
                    expectedSwitches=wheel_switch,expectedSame=wheel_same))


def report(data):
    out=["# Waiting inside the door lattice", "",
         f"Exact sieve through {data['limit']:,}; ingredients 5, 7, 49 and 11. No probable-prime tests.", "",
         "A miss is an eligible composite position between consecutive prime hires. A numeric gap is the difference between the prime endpoints. After filtering, a miss means a composite not eliminated by primes at most 100. A small prime is never eliminated merely because it equals the trial divisor.", "",
         "Only intervals with both endpoints inside a band enter its wait distribution. Leading/trailing boundary runs are reported separately in JSON. First hires are not pooled with subsequent waits. Powers and different ingredients overlap, so lanes are not independent datasets.", "",
         "## Whole-window census", "",
         "| Q | Candidates | Prime hires | Mean misses | 90th percentile | Maximum misses | After ≤100 sieve: mean misses |",
         "|---:|---:|---:|---:|---:|---:|---:|"]
    for r in data['overall']:
        m,f=r['candidateMisses'],r['survivorMisses']
        out.append(f"| {r['q']} | {r['candidates']:,} | {r['primeHits']:,} | {m['mean']:.3f} | {m['p90']} | {m['maximum']} | {f['mean']:.3f} |")
    out += ["", "First hires (kept separate): " + "; ".join(f"Q={r['q']}: {r['boundary']['firstPrime']}, {r['boundary']['leadingMisses']} preceding misses" for r in data['overall']) + ". All four happen to succeed at their first eligible position; this selection is not representative of all ingredients."]
    out += ["", "## Moving along the number line", "",
            "| Q | Band (lower exclusive) | Mean misses | After sieve: mean misses | After sieve: immediate next survivor prime | Fitted independent baseline |",
            "|---:|---|---:|---:|---:|---:|"]
    for r in data['bands']:
        m,f=r['candidateMisses'],r['survivorMisses']
        observed=f['histogram'].get('0',0)/f['count']
        out.append(f"| {r['q']} | ({r['lowerExclusive']:,}, {r['upperInclusive']:,}] | {m['mean']:.3f} | {f['mean']:.3f} | {observed:.2%} | {r['survivorSuccessRate']:.2%} |")
    out += ["", "## Residue transitions", "",
            "| Q | Switch class | Same class | Switch share | Equal-hazard independent baseline |",
            "|---:|---:|---:|---:|---:|"]
    for r in data['overall']:
        t=r['transitions'];switch=t.get('0->1',0)+t.get('1->0',0);same=t.get('0->0',0)+t.get('1->1',0)
        out.append(f"| {r['q']} | {switch:,} | {same:,} | {switch/(switch+same):.2%} | {r['independentBaseline']['switchFraction']:.2%} |")
    out += ["", "Classes alternate at candidate level. With M missed candidate positions, a successful transition switches class iff M is even. Under an independent constant success probability h, its switching fraction would be 1/(2−h), not 1/2. The comparison assumes equal hazards for the two classes; their empirical counts are in the JSON.", "",
            "## Accounting for the small-prime blocking pattern", "",
            "Keep the actual candidate positions surviving the <=100 sieve, including their residue-class order, and independently label each a success with the band's observed survivor success rate. The expected transition counts below are calculated analytically, not by random simulation. This is a fitted comparison, not a significance test.", "",
            "| Q | Band | Observed switch share | Raw independent model | Sieve-aware independent model |",
            "|---:|---|---:|---:|---:|"]
    for r in data['bands']:
        if r['lowerExclusive'] < 1000000:
            continue
        t=r['transitions'];switch=t.get('0->1',0)+t.get('1->0',0);total=sum(t.values())
        out.append(f"| {r['q']} | ({r['lowerExclusive']:,}, {r['upperInclusive']:,}] | {switch/total:.2%} | {r['independentBaseline']['switchFraction']:.2%} | {r['sieveAwareBaseline']['switchFraction']:.2%} |")
    out += ["",
            "## Composite blockers", "",
            "A composite is assigned only its smallest prime factor; the categories are disjoint. The >100 category is the surviving composite population, not an assertion of primality.", "",
            "| Q | Composites | Blocked by primes ≤100 | Share removed | Most frequent smallest blockers |",
            "|---:|---:|---:|---:|---|"]
    for r in data['overall']:
        b=r['smallestBlockers'];comp=r['candidates']-r['primeHits'];removed=comp-b.get('>100',0)
        top=sorted(((int(k),v) for k,v in b.items() if k!='>100'),key=lambda t:(-t[1],t[0]))[:5]
        out.append(f"| {r['q']} | {comp:,} | {removed:,} | {removed/comp:.2%} | " + "; ".join(f"{p}: {n:,}" for p,n in top) + " |")
    out += ["", "## Longest complete waits", "", "| Q | Prime endpoints | Missed opportunities | Surviving misses after sieve | Number-line gap |", "|---:|---|---:|---:|---:|"]
    for r in data['overall']:
        w=r['longest'];out.append(f"| {r['q']} | {w['start']:,} → {w['end']:,} | {w['misses']} | {w['survivingMisses']} | {w['numericGap']:,} |")
    out += ["", "## Interpretation limits", "",
            "The 7 and 49 lanes have nearly equal waits when measured in candidate opportunities. This is consistent with the classical density calculation: the candidate count is asymptotic to X/(3Q), while covered prime count is asymptotic to Li(X)/phi(Q). For Q=q^a, the ratio Q/phi(Q)=q/(q−1) does not depend on a. Higher powers thin both candidate positions and prime hits. Their number-line gaps still grow.", "",
            "Below 10,000, removal by all primes at most 100 removes every composite, since a composite has a prime factor at most its square root. Zero post-sieve misses in that band are therefore guaranteed, not an empirical discovery.", "",
            "The geometric baseline is descriptive. Prime density changes across broad bands, residue classes have local restrictions, and pair correlations can remain after sieving. These comparisons do not establish a new law, statistical significance, or a bound on the next prime. The mean wait is largely determined by the number of successes: it is not by itself evidence of independence. Inspect zero-miss frequencies, tails, transitions and blockers separately.", "",
            "For a blocking prime r not dividing 6Q, each candidate branch hits one blocked residue of its branch index modulo r. Thus the blocking pattern repeats with r within each branch, although composites may have several blockers. Removing small blockers leaves larger ones; it does not create independent trials.", "",
            "Reproduce: `python3 analysis/door-coverage/waits.py --limit 10000000`. Full histograms, class counts, censored edges and factor counts are in `waits-results.json`.", ""]
    return '\n'.join(out)


if __name__ == '__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--limit',type=int,default=10_000_000)
    args=parser.parse_args()
    if args.limit<100000:
        parser.error('Use a limit of at least 100000')
    start=time.perf_counter();spf=sieve(args.limit)
    overall=[analyze(q,spf,0,args.limit) for q in QS]
    bounds=sorted(set([0,10000,100000]+[x for x in (1000000,10000000) if x<args.limit]+[args.limit]))
    bands=[analyze(q,spf,lo,hi) for q in QS for lo,hi in zip(bounds,bounds[1:])]
    data=dict(limit=args.limit,smallFactorBound=BOUND,ingredients=QS,overall=overall,bands=bands)
    here=Path(__file__).resolve().parent
    (here/'waits-results.json').write_text(json.dumps(data,indent=2)+'\n')
    (here/'waits-report.md').write_text(report(data))
    print(report(data));print(f'Runtime: {time.perf_counter()-start:.2f}s')
