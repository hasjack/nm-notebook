#!/usr/bin/env python3
"""Thin hunt: first owners of an odd prime door q ≠ 3 (q ≡ 1 or 2 mod 3).

Finds primes p with q | m0(p), p >= 2q-1.
Two CRT classes mod 3q (always solvable since gcd(q,3)=1):
  A: p ≡ -1 (mod q), p ≡ 1 (mod 3)  → m0(p)=p+1
  B: p ≡  1 (mod q), p ≡ 2 (mod 3)  → m0(p)=p-1

Usage:
  python3 thin_owner_of_q.py 300647710579 --count 5
  python3 thin_owner_of_q.py 98784247763 --count 5   # q ≡ 2 mod 3
"""
from __future__ import annotations
import argparse
import time

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

def scan(q: int, want: int):
    assert q > 3 and q % 2 == 1 and q % 3 != 0
    assert q % 3 in (1, 2), "q must be ≡ 1 or 2 (mod 3)"
    mod = 3 * q
    floor = 2 * q - 1
    rA = crt(q - 1, q, 1, 3)
    rB = crt(1, q, 2, 3)
    print(f"q={q}  (q mod 3 = {q % 3})")
    print(f"floor={floor}  mod={mod}")
    print(f"class A residue={rA}  class B residue={rB}")

    def walk(res, label):
        x = res + ((floor - res + mod - 1) // mod) * mod
        if x < floor:
            x += mod
        found = []
        tested = 0
        while len(found) < want:
            tested += 1
            if is_prime(x):
                m0 = x + (1 if x % 3 == 1 else -1)
                assert m0 % q == 0
                found.append((x, m0 // q))
                print(f"  {label} owner {len(found)}: p={x}  m0/q={m0 // q}", flush=True)
            x += mod
        return found, tested

    t0 = time.perf_counter()
    a, ta = walk(rA, "A")
    b, tb = walk(rB, "B")
    merged = sorted([(p, "A", k) for p, k in a] + [(p, "B", k) for p, k in b])
    print("\nFirst owners by size:")
    for i, (p, lab, k) in enumerate(merged[:want], 1):
        print(f"  {i}. p={p}  class={lab}  m0/q={k}")
    print(f"\nSmallest owner: {merged[0][0]}")
    print(f"Candidates tested: A {ta}, B {tb}")
    print(f"Wall: {time.perf_counter()-t0:.4f}s")
    return merged

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("q", type=int, help="odd prime door ≡ 1 or 2 mod 3")
    ap.add_argument("--count", type=int, default=5)
    args = ap.parse_args()
    scan(args.q, args.count)
