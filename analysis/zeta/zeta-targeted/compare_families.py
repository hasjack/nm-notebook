#!/usr/bin/env python3
"""Census: k ≡ 2 (mod 12) versus the extra even k with 3 ∤ k.

    python3 compare_families.py --max-k 10000
"""
import argparse, json, math, sys
from collections import defaultdict
from pathlib import Path
import hunt

sys.set_int_max_str_digits(0)

def factor(n):
    out = {}
    p = 2
    while p * p <= n:
        while n % p == 0:
            out[p] = out.get(p, 0) + 1
            n //= p
        p += 1
    if n > 1:
        out[n] = 1
    return out

def census(max_k):
    fam = {
        2: defaultdict(int),
        "extra": defaultdict(int),
    }
    seen_D = {2: set(), "extra": set()}
    seen_plus = {2: set(), "extra": set()}
    seen_elig = {2: set(), "extra": set()}
    for k in range(2, max_k + 1, 2):
        if k % 3 == 0:
            continue
        key = 2 if k % 12 == 2 else "extra"
        fam[key]["indices"] += 1
        _, d, _ = hunt.denominator(factor(k))
        D = 3 * d
        if D not in seen_D[key]:
            seen_D[key].add(D)
            fam[key]["distinct_D"] += 1
        else:
            fam[key]["repeat_D"] += 1
        plus = d + 1
        elig = d + 1 if d % 3 == 1 else d - 1
        fam[key]["plus_side"] += int(elig == plus)
        fam[key]["minus_side"] += int(elig != plus)
        if hunt.is_prime(plus):
            fam[key]["plus_prime"] += 1
            seen_plus[key].add(plus)
        if hunt.is_prime(elig):
            fam[key]["eligible_prime"] += 1
            seen_elig[key].add(elig)
    out = {}
    for key in (2, "extra"):
        row = dict(fam[key])
        row["distinct_plus_primes"] = len(seen_plus[key])
        row["distinct_eligible_primes"] = len(seen_elig[key])
        out[str(key)] = row
    out["max_k"] = max_k
    return out

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--max-k", type=int, default=10000)
    ap.add_argument("--out", type=Path, default=None)
    args = ap.parse_args()
    report = census(args.max_k)
    print(json.dumps(report, indent=2))
    if args.out:
        args.out.write_text(json.dumps(report, indent=2))

if __name__ == "__main__":
    main()
