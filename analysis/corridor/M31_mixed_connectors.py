#!/usr/bin/env python3
"""Hunt mixed M31 connectors that beat the direct-bridge seating time τ(v).

Scans all M-owners p with floor ≤ p < (τ(v)+1)/2, classifies m0(p)/M as
pure (power of 2) vs mixed (odd prime factor), and for early mixed owners
computes τ(p) = first owner of p.
"""
from __future__ import annotations
import time
from collections import Counter

# Reuse MR + CRT from thin_owners / thin_owner_of_q
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

def factor_small(n: int) -> list[int]:
    """Trial-factor n (expected small for M31 owners below our cap)."""
    facs = []
    while n % 2 == 0:
        facs.append(2)
        n //= 2
    f = 3
    while f * f <= n:
        while n % f == 0:
            facs.append(f)
            n //= f
        f += 2
    if n > 1:
        facs.append(n)
    return facs

def m0(p: int) -> int:
    return p + (1 if p % 3 == 1 else -1)

def first_owners(q: int, want: int = 5):
    """Return sorted list of (p, class, m0/q) first owners of door q."""
    assert q > 3 and q % 2 == 1 and q % 3 in (1, 2)
    mod = 3 * q
    floor = 2 * q - 1
    rA = crt(q - 1, q, 1, 3)
    rB = crt(1, q, 2, 3)

    def walk(res, label):
        x = res + ((floor - res + mod - 1) // mod) * mod
        if x < floor:
            x += mod
        found = []
        while len(found) < want:
            if is_prime(x):
                assert m0(x) % q == 0
                found.append((x, label, m0(x) // q))
            x += mod
        return found

    return sorted(walk(rA, "A") + walk(rB, "B"))

def classify_k(k: int):
    facs = factor_small(k)
    odd = [f for f in facs if f != 2]
    pure = len(odd) == 0
    direct5 = 5 in facs
    return {
        "k": k,
        "factors": facs,
        "odd_primes": sorted(set(odd)),
        "pure": pure,
        "mixed": not pure,
        "direct5": direct5,
        "factorization": " * ".join(f"{p}^{e}" if e > 1 else str(p)
                                    for p, e in sorted(Counter(facs).items()))
                         or "1",
    }

def scan_M_owners(M: int, cap: int):
    """All M-owners with floor ≤ p < cap."""
    mod = 3 * M
    floor = 2 * M - 1
    rA = crt(M - 1, M, 1, 3)
    rB = crt(1, M, 2, 3)
    owners = []
    tested = {"A": 0, "B": 0}

    def walk(res, label):
        x = res + ((floor - res + mod - 1) // mod) * mod
        if x < floor:
            x += mod
        while x < cap:
            tested[label] += 1
            if is_prime(x):
                k = m0(x) // M
                assert m0(x) % M == 0
                info = classify_k(k)
                owners.append((x, label, info))
            x += mod

    walk(rA, "A")
    walk(rB, "B")
    owners.sort(key=lambda t: t[0])
    return owners, tested

def main():
    M = 2147483647  # M31
    r0 = 98784247763
    v = 300647710579
    tau_v = 24051816846319
    floor = 2 * M - 1
    mod = 3 * M
    cap = (tau_v + 1) // 2  # p < this can possibly have τ(p) < τ(v)

    print("=" * 60)
    print("M31 mixed connectors hunt")
    print("=" * 60)
    print(f"M={M}")
    print(f"r0={r0}")
    print(f"v={v}")
    print(f"tau(v)={tau_v}")
    print(f"floor={floor}  mod={mod}  cap={cap}")
    print()

    # --- τ(r0) ---
    print("--- τ(r0): first owners of r0 ---")
    t0 = time.perf_counter()
    r0_owners = first_owners(r0, want=5)
    tau_r0 = r0_owners[0][0]
    tau_r0_class = r0_owners[0][1]
    print(f"τ(r0)={tau_r0}  class={tau_r0_class}  m0/r0={r0_owners[0][2]}")
    print("Next few:")
    for i, (p, lab, k) in enumerate(r0_owners[:5], 1):
        print(f"  {i}. p={p}  class={lab}  m0/r0={k}")
    print(f"Wall τ(r0): {time.perf_counter()-t0:.4f}s")
    print(f"τ(r0) < τ(v)? {tau_r0 < tau_v}  ratio τ(v)/τ(r0)={tau_v/tau_r0:.6f}")
    print()

    # --- scan all M-owners below cap ---
    print("--- Scan M-owners below cap ---")
    t1 = time.perf_counter()
    owners, tested = scan_M_owners(M, cap)
    wall_scan = time.perf_counter() - t1
    n_pure = sum(1 for _, _, info in owners if info["pure"])
    n_mixed = sum(1 for _, _, info in owners if info["mixed"])
    n_d5 = sum(1 for _, _, info in owners if info["direct5"])
    print(f"Scanned owners: {len(owners)}  (tested A={tested['A']} B={tested['B']})")
    print(f"pure={n_pure}  mixed={n_mixed}  direct-5={n_d5}")
    print(f"Wall scan: {wall_scan:.4f}s")
    print()

    # Verify r0 is first owner and mixed
    assert owners[0][0] == r0, f"expected r0 first, got {owners[0][0]}"
    assert owners[0][2]["mixed"], "r0 should be mixed"

    # List first mixed owners
    mixed = [(p, lab, info) for p, lab, info in owners if info["mixed"]]
    print(f"First 20 mixed owners (of {len(mixed)}):")
    for i, (p, lab, info) in enumerate(mixed[:20], 1):
        print(f"  {i}. p={p}  class={lab}  k={info['k']}={info['factorization']}"
              f"  odd={info['odd_primes']}  d5={info['direct5']}")
    print()

    # Pure owners (first few)
    pure = [(p, lab, info) for p, lab, info in owners if info["pure"]]
    print(f"First 10 pure owners (of {len(pure)}):")
    for i, (p, lab, info) in enumerate(pure[:10], 1):
        print(f"  {i}. p={p}  class={lab}  k={info['k']}={info['factorization']}")
    print()

    # --- τ(p) for mixed owners that could beat τ(r0) ---
    # Need 2p-1 < τ(r0), i.e. p < (τ(r0)+1)/2
    beat_r0_cap = (tau_r0 + 1) // 2
    candidates = [(p, lab, info) for p, lab, info in mixed if p < beat_r0_cap]
    print(f"--- τ(p) for mixed owners with p < (τ(r0)+1)/2 = {beat_r0_cap} ---")
    print(f"Candidates that could beat τ(r0): {len(candidates)}")

    tau_results = []
    t2 = time.perf_counter()
    for p, lab, info in candidates:
        ow = first_owners(p, want=1)
        tp, tlab, tk = ow[0]
        tau_results.append((tp, p, lab, info, tlab, tk))
        print(f"  τ({p})={tp}  class={tlab}  m0/p={tk}  "
              f"k={info['factorization']}  beats_r0={tp < tau_r0}", flush=True)
    print(f"Wall τ-sweep: {time.perf_counter()-t2:.4f}s")
    print()

    # Also compute τ for a few more early mixed beyond beat_r0_cap for the record
    # (they cannot beat τ(r0) since τ(p)≥2p-1≥τ(r0), but report τ(v) comparison)
    extra = [m for m in mixed if m[0] >= beat_r0_cap][:5]
    print(f"--- Sample τ(p) for next mixed (cannot beat τ(r0) by floor) ---")
    for p, lab, info in extra:
        # Only report floor bound; skip full hunt if 2p-1 >= tau_v already
        flo = 2 * p - 1
        if flo >= tau_v:
            print(f"  p={p}  floor τ≥{flo} ≥ τ(v); skip")
            continue
        ow = first_owners(p, want=1)
        tp, tlab, tk = ow[0]
        print(f"  τ({p})={tp}  class={tlab}  m0/p={tk}  "
              f"k={info['factorization']}  <τ(v)? {tp < tau_v}", flush=True)
        tau_results.append((tp, p, lab, info, tlab, tk))
    print()

    # Best mixed connecting time among those we computed
    if tau_results:
        best = min(tau_results, key=lambda t: t[0])
        print("=" * 60)
        print(f"EARLIEST mixed τ found: {best[0]}")
        print(f"  via owner p={best[1]} class={best[2]}  m0/M={best[3]['factorization']}")
        print(f"  τ(p) class={best[4]}  m0/p={best[5]}")
        print(f"  vs τ(v)={tau_v}: beats={best[0] < tau_v}  ratio={tau_v/best[0]:.6f}")
        print(f"  vs τ(r0)={tau_r0}: same_as_r0={best[1]==r0}")
        print("=" * 60)

    # Sanity: v is among owners
    v_hit = [o for o in owners if o[0] == v]
    print(f"\nv={v} in scan? {bool(v_hit)}")
    if v_hit:
        print(f"  class={v_hit[0][1]}  k={v_hit[0][2]['factorization']}  "
              f"mixed={v_hit[0][2]['mixed']}  direct5={v_hit[0][2]['direct5']}")

    # Write results dict for markdown
    results = {
        "M": M, "r0": r0, "v": v, "tau_v": tau_v,
        "floor": floor, "mod": mod, "cap": cap,
        "tau_r0": tau_r0, "tau_r0_class": tau_r0_class,
        "r0_owners": r0_owners,
        "n_owners": len(owners), "n_pure": n_pure, "n_mixed": n_mixed,
        "n_direct5": n_d5, "tested": tested,
        "wall_scan": wall_scan,
        "mixed_first20": mixed[:20],
        "pure_first10": pure[:10],
        "tau_results": tau_results,
        "beat_r0_cap": beat_r0_cap,
        "n_candidates_beat_r0": len(candidates),
        "best": best if tau_results else None,
        "owners_all_mixed_p": [p for p, _, _ in mixed],
        "all_owners_summary": [
            (p, lab, info["k"], info["factorization"], info["mixed"], info["direct5"])
            for p, lab, info in owners
        ],
    }
    return results

if __name__ == "__main__":
    main()
