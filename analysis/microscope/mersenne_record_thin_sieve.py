#!/usr/bin/env python3
"""Thin sieve: certified first-owner multiplier floor for Mersenne door q = 2^e - 1.

Does NOT hunt τ(q) and never materializes q. Works only with (k * q_mod_r) % r.

Hire door facts (e odd ⇒ q ≡ 1 (mod 3)):
  m0(q) = q + 1 = 2^e  (pure 2-power sink)
  First-owner candidates: primes p = kq ± 1 with admissible k ≡ 2 or 4 (mod 6)
    k ≡ 2 (mod 6) → class A: p = kq - 1, m0(p) = p + 1 = kq
    k ≡ 4 (mod 6) → class B: p = kq + 1, m0(p) = p - 1 = kq
  Elementary floor: τ(q) ≥ 2q - 1 ⇒ K ≥ 2.

Certified floor: for each odd prime r ≤ R, eliminate admissible k with
  k·q ≡ ±1 (mod r) (matching class), provided kq±1 ≠ r.
K_cert = first admissible k that survives all r ≤ R.
Then every admissible multiplier < K_cert has a prime factor ≤ R in its
candidate p = kq±1, hence is composite, so the first owner has k ≥ K_cert.

Usage:
  python3 mersenne_record_thin_sieve.py --e 31 --R 100000          # sanity (expect 46)
  python3 mersenne_record_thin_sieve.py --e 136279841 --R 1000000
  python3 mersenne_record_thin_sieve.py --e 136279841 --R 10000000
"""
from __future__ import annotations

import argparse
import math
import time
from typing import List, Optional, Tuple


def sieve_primes(limit: int) -> List[int]:
    if limit < 2:
        return []
    n = limit + 1
    is_p = bytearray(b"\x01") * n
    is_p[0] = is_p[1] = 0
    for i in range(2, int(math.isqrt(limit)) + 1):
        if is_p[i]:
            step = i
            start = i * i
            is_p[start:n:step] = b"\x00" * (((n - 1 - start) // step) + 1)
    return [i for i in range(2, n) if is_p[i]]


def admissible_k_iter(start: int = 2):
    """Yield k = 2,4,8,10,14,... (≡ 2 or 4 mod 6), starting at >= start."""
    k = start if start >= 2 else 2
    # snap to next admissible
    while k % 6 not in (2, 4):
        k += 1
    while True:
        yield k
        if k % 6 == 2:
            k += 2  # 2 -> 4
        else:
            k += 4  # 4 -> 8


def build_forbidden(
    e: int, primes: List[int]
) -> Tuple[List[int], List[int], List[int], int]:
    """For each odd prime r, store forbidden residue of k mod r for classes A/B.

    Returns (rs, forb_A, forb_B, skipped_qmod0) aligned lists (r > 2 only, qmod≠0).
    """
    rs: List[int] = []
    forb_A: List[int] = []
    forb_B: List[int] = []
    skipped = 0
    for r in primes:
        if r == 2:
            continue
        qmod = pow(2, e, r) - 1
        if qmod < 0:
            qmod += r
        if qmod == 0:
            skipped += 1
            continue
        inv = pow(qmod, -1, r)
        rs.append(r)
        forb_A.append(inv)  # k ≡ q^{-1}  ⇒ kq ≡ 1  ⇒ p=kq-1 ≡ 0
        forb_B.append((r - inv) % r)  # k ≡ -q^{-1} ⇒ kq ≡ -1 ⇒ p=kq+1 ≡ 0
    return rs, forb_A, forb_B, skipped


def first_survivor(
    rs: List[int],
    forb_A: List[int],
    forb_B: List[int],
    k_cap: int,
) -> Tuple[Optional[int], int, Optional[int]]:
    """Walk admissible k; return (K_cert, n_ruled, hit_prime_of_last_ruled_or_None)."""
    ruled = 0
    last_hit: Optional[int] = None
    for k in admissible_k_iter(2):
        if k > k_cap:
            return None, ruled, last_hit
        is_A = k % 6 == 2
        hit = None
        if is_A:
            for r, fa in zip(rs, forb_A):
                if k % r == fa:
                    # candidate p = kq-1 ≡ 0 (mod r); p = r only if kq = r+1
                    # impossible for k≥2 and r ≤ R ≪ q — no equality check needed
                    hit = r
                    break
        else:
            for r, fb in zip(rs, forb_B):
                if k % r == fb:
                    hit = r
                    break
        if hit is not None:
            ruled += 1
            last_hit = hit
            continue
        return k, ruled, last_hit
    return None, ruled, last_hit  # pragma: no cover


def mark_sieve_first(
    rs: List[int],
    forb_A: List[int],
    forb_B: List[int],
    k_cap: int,
) -> Tuple[Optional[int], int]:
    """Faster path: mark eliminated admissible slots in a bit array up to k_cap."""
    # index by k; only care about admissible
    killed = bytearray(k_cap + 1)
    for r, fa, fb in zip(rs, forb_A, forb_B):
        # mark all k ≡ fa (mod r) with k ≡ 2 (mod 6), and k ≡ fb with k ≡ 4 (mod 6)
        # walk k = fa, fa+r, ... and check mod 6
        if fa <= k_cap:
            k = fa
            while k < 2:
                k += r
            while k <= k_cap:
                if k % 6 == 2:
                    killed[k] = 1
                k += r
        if fb <= k_cap:
            k = fb
            while k < 2:
                k += r
            while k <= k_cap:
                if k % 6 == 4:
                    killed[k] = 1
                k += r
    ruled = 0
    for k in admissible_k_iter(2):
        if k > k_cap:
            return None, ruled
        if killed[k]:
            ruled += 1
            continue
        return k, ruled
    return None, ruled


def run(e: int, R: int, k_cap: int, method: str) -> dict:
    t0 = time.perf_counter()
    primes = sieve_primes(R)
    t_sieve = time.perf_counter()
    rs, forb_A, forb_B, skipped = build_forbidden(e, primes)
    t_forb = time.perf_counter()
    if method == "mark":
        K, ruled = mark_sieve_first(rs, forb_A, forb_B, k_cap)
        last_hit = None
    else:
        K, ruled, last_hit = first_survivor(rs, forb_A, forb_B, k_cap)
    t1 = time.perf_counter()
    return {
        "e": e,
        "R": R,
        "K_cert": K,
        "ruled_below": ruled,
        "n_primes": len(primes),
        "n_active_r": len(rs),
        "skipped_qmod0": skipped,
        "k_cap": k_cap,
        "method": method,
        "wall_s": t1 - t0,
        "sieve_primes_s": t_sieve - t0,
        "build_forb_s": t_forb - t_sieve,
        "walk_s": t1 - t_forb,
        "last_hit": last_hit,
    }


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--e", type=int, default=136279841, help="Mersenne exponent")
    ap.add_argument("--R", type=int, default=1_000_000, help="sieve prime bound")
    ap.add_argument("--k-cap", type=int, default=100_000, help="max admissible k to search")
    ap.add_argument("--method", choices=("walk", "mark"), default="mark")
    ap.add_argument("--validate-m31", action="store_true", help="run e=31 R=1e5 expect K=46")
    ap.add_argument("--kill-table", type=int, default=0,
                    help="if >0, print first-hit r for each admissible k ≤ this value")
    args = ap.parse_args()


    if args.kill_table:
        primes = sieve_primes(args.R)
        print("k\tclass\thit_r", flush=True)
        for k in admissible_k_iter(2):
            if k > args.kill_table:
                break
            is_A = k % 6 == 2
            hit = None
            for r in primes:
                if r == 2:
                    continue
                qmod = pow(2, args.e, r) - 1
                if qmod < 0:
                    qmod += r
                if qmod == 0:
                    continue
                val = (k * qmod) % r
                if is_A and val == 1:
                    hit = r
                    break
                if (not is_A) and val == (r - 1):
                    hit = r
                    break
            print(f"{k}\t{'A' if is_A else 'B'}\t{hit}", flush=True)
        return

    if args.validate_m31:
        args.e, args.R, args.k_cap = 31, 100_000, 1000

    print(f"e={args.e}  R={args.R}  k_cap={args.k_cap}  method={args.method}", flush=True)
    out = run(args.e, args.R, args.k_cap, args.method)
    print(
        f"K_cert={out['K_cert']}  ruled_below={out['ruled_below']}  "
        f"active_r={out['n_active_r']}/{out['n_primes']}  qmod0_skip={out['skipped_qmod0']}",
        flush=True,
    )
    print(
        f"wall={out['wall_s']:.4f}s  (primes {out['sieve_primes_s']:.4f}s, "
        f"forb {out['build_forb_s']:.4f}s, walk/mark {out['walk_s']:.4f}s)",
        flush=True,
    )
    if args.validate_m31:
        assert out["K_cert"] == 46, out
        print("M31 validation OK: K_cert=46", flush=True)
    # machine-readable one-liner
    print(
        f"RESULT e={out['e']} R={out['R']} K_cert={out['K_cert']} "
        f"wall_s={out['wall_s']:.4f} ruled={out['ruled_below']}",
        flush=True,
    )


if __name__ == "__main__":
    main()
