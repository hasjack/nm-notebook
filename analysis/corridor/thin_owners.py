#!/usr/bin/env python3
"""Thin hunt: first owners of M_n = 2^n - 1 (Mersenne prime door).

Finds primes p with M | m0(p), p >= 2M-1.
Two CRT classes mod 3M (assumes M ≡ 1 mod 3, as for M31/M61):
  A: p ≡ -1 (mod M), p ≡ 1 (mod 3)
  B: p ≡  1 (mod M), p ≡ 2 (mod 3)

Usage:
  python3 thin_owners.py 61          # M61
  python3 thin_owners.py 31 --count 10
"""
from __future__ import annotations
import argparse

# Deterministic MR for n < 2^64 (sufficient near M61 floor ~4e18)
_WIT = (2, 3, 5, 7, 11, 13, 23)

def is_prime(n: int) -> bool:
    if n < 2:
        return False
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29):
        if n == p:
            return True
        if n % p == 0:
            return False
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in _WIT:
        if a % n == 0:
            continue
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            continue
        for _ in range(s - 1):
            x = (x * x) % n
            if x == n - 1:
                break
        else:
            return False
    return True

def crt(a1, m1, a2, m2):
    inv = pow(m1, -1, m2)
    return (a1 + m1 * ((a2 - a1) * inv % m2)) % (m1 * m2)

def scan(n: int, want: int):
    M = (1 << n) - 1
    assert M % 3 == 1, "this script assumes M ≡ 1 (mod 3) like M31/M61"
    mod = 3 * M
    floor = 2 * M - 1
    rA = crt(M - 1, M, 1, 3)
    rB = crt(1, M, 2, 3)
    print(f"M_{n}={M}")
    print(f"floor={floor}  mod={mod}")
    print(f"class A residue={rA}  class B residue={rB}")

    def walk(res, label):
        x = res + ((floor - res + mod - 1) // mod) * mod
        if x < floor:
            x += mod
        found = []
        while len(found) < want:
            if is_prime(x):
                m0 = x + (1 if x % 3 == 1 else -1)
                assert m0 % M == 0
                found.append((x, m0 // M))
                print(f"  {label} owner {len(found)}: p={x}  m0/M={m0 // M}", flush=True)
            x += mod
        return found

    a = walk(rA, "A")
    b = walk(rB, "B")
    merged = sorted([(p, "A", k) for p, k in a] + [(p, "B", k) for p, k in b])
    print("\nFirst owners by size:")
    for i, (p, lab, k) in enumerate(merged[:want], 1):
        print(f"  {i}. p={p}  class={lab}  m0/M={k}")
    print(f"\nSmallest owner: {merged[0][0]}")

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("n", type=int, help="Mersenne exponent (31, 61, …)")
    ap.add_argument("--count", type=int, default=5)
    args = ap.parse_args()
    scan(args.n, args.count)
