#!/usr/bin/env python3
"""Three-state classification of von Staudt candidates p = d+1.

States: prime | composite | unresolved.

- p < 2^64: Jaeschke Miller–Rabin (deterministic).
- p >= 2^64 with p-1 fully factored over the index primes: Pocklington with
  bases 2..501. Fermat failure => composite. No witness in range => unresolved.
- Never treat search-fail as composite / omit.

Publication rule: a denominator receipt is exact only if unresolved == 0.
"""
from __future__ import annotations

import math
from functools import lru_cache

LIM = 2**64
DEFAULT_BASES = range(2, 502)

try:
    import gmpy2

    def modpow(a, e, m):
        return int(gmpy2.powmod(int(a), int(e), int(m)))
except ImportError:

    def modpow(a, e, m):
        return pow(int(a), int(e), int(m))


@lru_cache(maxsize=200000)
def isprime64(n: int) -> bool:
    if not 2 <= n < LIM:
        return False
    if n % 2 == 0:
        return n == 2
    odd = n - 1
    power = 0
    while odd % 2 == 0:
        odd //= 2
        power += 1
    for a in (2, 325, 9375, 28178, 450775, 9780504, 1795265022):
        if a % n == 0:
            continue
        v = pow(a, odd, n)
        for j in range(power):
            if v == n - 1 or (j == 0 and v == 1):
                break
            v = v * v % n
        else:
            return False
    return True


def factor_over(n, primes):
    out = {}
    t = int(n)
    for p in primes:
        e = 0
        while t % p == 0:
            t //= p
            e += 1
        if e:
            out[int(p)] = e
    return out, t


def classify_origin(n, index_primes, bases=DEFAULT_BASES):
    """Return (state, detail) with state in {prime, composite, unresolved}.

    detail is a short tag, or a witness dict when state == prime and n >= 2^64.
    """
    n = int(n)
    if n < 2:
        return "composite", "lt2"
    if n < LIM:
        return ("prime", "isprime64") if isprime64(n) else ("composite", "isprime64")

    primes = tuple(int(p) for p in index_primes)
    factors, rest = factor_over(n - 1, primes)
    if rest != 1:
        for a in bases:
            g = math.gcd(a, n)
            if g != 1:
                if 1 < g < n:
                    return "composite", f"factor:{g}"
                continue
            if modpow(a, n - 1, n) != 1:
                return "composite", f"fermat:{a}"
        return "unresolved", "p-1_not_over_index"

    if not factors or not all(isprime64(p) for p in factors):
        return "unresolved", "bad_index_factors"

    F = n - 1
    if F * F <= n:
        return "unresolved", "F2_le_n"

    witnesses = {}
    for p in factors:
        found = None
        for a in bases:
            g = math.gcd(a, n)
            if g != 1:
                if 1 < g < n:
                    return "composite", f"factor:{g}"
                continue
            if modpow(a, n - 1, n) != 1:
                return "composite", f"fermat:{a}"
            if math.gcd(modpow(a, (n - 1) // p, n) - 1, n) == 1:
                found = a
                break
        if found is None:
            return "unresolved", f"no_witness_p={p}"
        witnesses[p] = found
    return "prime", witnesses


def rebuild_denominator(k, index_factors, progress_every=500, log=None):
    """Rebuild D_k from index with three-state accounting.

    Returns dict with keys: D, counts, unresolved (list of (p, detail)),
    primes_included (list).
    """
    f = {int(p): int(e) for p, e in index_factors.items()}
    index_primes = tuple(f)
    ds = {1}
    for p, e in f.items():
        expanded = set()
        for d in ds:
            t = d
            for _ in range(e + 1):
                expanded.add(t)
                t *= p
        ds = expanded

    counts = {"prime": 0, "composite": 0, "unresolved": 0}
    unresolved = []
    included = []
    D = 1
    total = len(ds)
    for i, d in enumerate(sorted(ds), 1):
        p = d + 1
        state, detail = classify_origin(p, index_primes)
        counts[state] += 1
        if state == "unresolved":
            unresolved.append({"p": str(p), "detail": detail if isinstance(detail, str) else "prime_witnesses"})
        elif state == "prime":
            included.append(p)
            D *= p
            t = k
            while t % p == 0:
                D *= p
                t //= p
        if progress_every and log and (i % progress_every == 0 or i == total):
            log("origin %d/%d %s" % (i, total, counts))
    return {
        "D": D,
        "counts": counts,
        "unresolved": unresolved,
        "primes_included": included,
        "divisor_candidates": total,
    }


class OriginUnresolved(Exception):
    """Denominator build hit unresolved large d+1 candidates."""

    def __init__(self, unresolved):
        self.unresolved = unresolved
        super().__init__(f"origin unresolved: {len(unresolved)} candidates")
