#!/usr/bin/env python3
"""Count distinct Hire arcs by (q mod 5, (m0(p)/q) mod 5).

Standard-library only. Default owner window: p <= 1,000,000.
The main grids omit p <= 5, the hub q=2, and the exceptional q=5.
Each distinct prime divisor contributes once, regardless of multiplicity.
These are descriptive counts and exact congruence checks, NOT a
prime-pair statistical baseline or a primality predictor.

Usage: python3 hire_torus_mod5.py --limit 1000000 --output results.json
"""
import argparse
from array import array
import json
from pathlib import Path


def run(limit):
    spf = array('I', range(limit + 2))
    spf[0] = 0
    spf[1] = 1
    for p in range(2, int((limit + 1) ** .5) + 1):
        if spf[p] == p:
            for n in range(p * p, limit + 2, p):
                if spf[n] == n:
                    spf[n] = p
    cuts = sorted(set([v for v in [10000, 100000, limit] if v <= limit]))
    counts = {str(s): [[0] * 5 for _ in range(5)] for s in [1, -1]}
    examples = {str(s): [[None] * 5 for _ in range(5)] for s in [1, -1]}
    exceptions = {'owners_le_5_arcs': 0, 'hub_arcs': 0, 'q5_arcs': 0}
    snapshots = {}
    owners = 0
    arcs = 0
    for p in range(2, limit + 1):
        if spf[p] == p and p != 3:
            # chi_3(p)=+1 for p=1 mod 3; -1 for p=2 mod 3.
            # The hub owner p=2 is not part of the odd-prime construction.
            if p != 2:
                owners += 1
                sign = 1 if p % 3 == 1 else -1
                m = p + sign
                assert m % 2 == 0 and m % 3 != 0
                n = m
                while n > 1:
                    q = spf[n]
                    while n % q == 0:
                        n //= q
                    a = m // q
                    assert a * q == p + sign and q != 3
                    arcs += 1
                    if p <= 5:
                        exceptions['owners_le_5_arcs'] += 1
                    elif q == 2:
                        exceptions['hub_arcs'] += 1
                    elif q == 5:
                        exceptions['q5_arcs'] += 1
                    else:
                        r, b = q % 5, a % 5
                        assert r != 0 and (r*b) % 5 != sign % 5
                        counts[str(sign)][b][r] += 1
                        if examples[str(sign)][b][r] is None:
                            examples[str(sign)][b][r] = {'p': p, 'q': q, 'a': a}
        if p in cuts:
            snapshots[str(p)] = json.loads(json.dumps(counts))
    bulk = sum(sum(row) for grid in counts.values() for row in grid)
    assert bulk + sum(exceptions.values()) == arcs
    return {'limit': limit, 'owners': owners, 'all_arcs': arcs,
            'bulk_arcs': bulk, 'exceptions': exceptions,
            'counts': counts, 'examples': examples, 'snapshots': snapshots,
            'forbidden_violations': 0,
            'row': 'a mod 5', 'column': 'q mod 5',
            'forbidden_rule': 'a*q = sign (mod 5) implies p = 0 (mod 5)',
            'scope': 'p>5, q>3, q!=5; distinct prime divisors'}

if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--limit', type=int, default=1000000)
    ap.add_argument('--output', type=Path)
    args = ap.parse_args()
    if args.limit < 7:
        ap.error('limit must be at least 7')
    result = run(args.limit)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))
