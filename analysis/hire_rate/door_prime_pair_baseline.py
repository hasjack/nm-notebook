#!/usr/bin/env python3
"""Compare large Hire-door factors with local-density and prime-pair heuristics.

Requires Python 3 and NumPy. Default: X=100,000,000, u=0.7,0.8,0.9.
For each prime q >= X**u and even a not divisible by 3, set m=a*q.
The 3-free door rule selects p=m+1 if m%3==1, otherwise p=m-1.
Count only p<=X, weighted by log(q). Since q>sqrt(X+1) in these
runs, a door cannot contain two such factors or a repeated such factor.

Old prediction, conditional on the enumerated q being prime:
    log(q) * 3*q/(q-1)/log(p).
Pair prediction multiplies this by:
    (4*C2/3) * product((r-1)/(r-2), odd primes r dividing a).
C2 is the twin-prime constant. For the linear forms q and aq+/-1,
the unrestricted conditional density is 2*C2*product/log(p).
The selected modulo-3 class doubles it: the other q class makes p
zero modulo 3. Thus the selected density is 4*C2*product/log(p).
The q/(q-1) term is retained from the old convention (negligible here).
This is a conditional prime-pair heuristic, not a proof or a prediction
independent of the list of prime factors q. No constants are fitted.

Owner windows are disjoint quarters of [0,X], with a fixed q cutoff.
CSV rows contain log weights, not unweighted pair counts.
Approximate sieve memory: X bytes, plus ~8*pi(X) bytes for prime indices.
"""
import argparse
import csv
import math
import sys
import numpy as np

C2 = 0.6601618158468696


def multiplier_factor(a):
    n, factor, r = a, 1.0, 2
    while r*r <= n:
        if n % r == 0:
            if r > 2:
                factor *= (r-1)/(r-2)
            while n % r == 0:
                n //= r
        r += 1
    if n > 2:
        factor *= (n-1)/(n-2)
    return 4*C2*factor/3


def sieve(limit):
    flags = np.ones(limit+2, dtype=bool)
    flags[:2] = False
    for p in range(2, math.isqrt(limit+1)+1):
        if flags[p]:
            flags[p*p::p] = False
    return flags, np.flatnonzero(flags)


def run(limit, thresholds, output):
    flags, primes = sieve(limit)
    boundaries = np.array([0, limit//4, limit//2, 3*limit//4, limit])
    writer = csv.writer(output)
    writer.writerow(['X','u','scope','branch','p_lower_exclusive',
                     'p_upper_inclusive','multiplier','actual_log_weight',
                     'old_prediction','pair_prediction','pair_error_percent'])

    def emit(u, scope, branch, lo, hi, a, values):
        observed, old, pair = values
        error = '' if pair == 0 else 100*(observed/pair-1)
        writer.writerow([limit,u,scope,branch,lo,hi,a,
                         observed,old,pair,error])

    for u in thresholds:
        cutoff = limit**u
        totals = np.zeros((2,4,3))
        by_multiplier = {}
        for a in range(2, int((limit+1)/cutoff)+1, 2):
            if a % 3 == 0:
                continue
            lower = np.searchsorted(primes, cutoff, side='left')
            upper = np.searchsorted(primes, (limit+1)/a, side='right')
            q = primes[lower:upper]
            q = q[q > 3]
            door = a*q
            sign = np.where(door % 3 == 1, 1, -1)
            owner = door+sign
            valid = owner <= limit
            q, owner, sign = q[valid], owner[valid], sign[valid]
            weight = np.log(q)
            old = weight*3*q/(q-1)/np.log(owner)
            pair = old*multiplier_factor(a)
            owner_prime = flags[owner]
            cells = np.zeros((2,4,3))
            for j, sg in enumerate([1,-1]):
                for k in range(4):
                    selected = ((sign == sg) & (owner > boundaries[k]) &
                                (owner <= boundaries[k+1]))
                    cells[j,k] = [np.sum(weight[selected & owner_prime]),
                                  np.sum(old[selected]), np.sum(pair[selected])]
            totals += cells
            by_multiplier[a] = cells
        emit(u,'total','both',0,limit,'',totals.sum(axis=(0,1)))
        for j, label in enumerate(['plus','minus']):
            emit(u,'branch',label,0,limit,'',totals[j].sum(axis=0))
        for k in range(4):
            emit(u,'window','both',boundaries[k],boundaries[k+1],'',
                 totals[:,k].sum(axis=0))
            for j, label in enumerate(['plus','minus']):
                emit(u,'window_branch',label,boundaries[k],boundaries[k+1],
                     '',totals[j,k])
        for a, cells in by_multiplier.items():
            emit(u,'multiplier','both',0,limit,a,cells.sum(axis=(0,1)))
            for j, label in enumerate(['plus','minus']):
                emit(u,'multiplier_branch',label,0,limit,a,
                     cells[j].sum(axis=0))


def main():
    parser = argparse.ArgumentParser(description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--limit', type=int, default=100_000_000)
    parser.add_argument('--thresholds', nargs='+', type=float,
                        default=[0.7,0.8,0.9])
    parser.add_argument('--output', help='CSV path; otherwise write to stdout')
    args = parser.parse_args()
    if args.limit < 100 or any(not 0.5 < u < 1 for u in args.thresholds):
        parser.error('limit must be >=100 and each threshold between 0.5 and 1')
    if any(args.limit**u <= math.sqrt(args.limit+1) for u in args.thresholds):
        parser.error('factor cutoffs must exceed sqrt(limit+1)')
    if args.output:
        with open(args.output,'w',newline='') as output:
            run(args.limit,args.thresholds,output)
    else:
        run(args.limit,args.thresholds,sys.stdout)


if __name__ == '__main__':
    main()
