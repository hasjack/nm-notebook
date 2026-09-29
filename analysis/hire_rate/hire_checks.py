#!/usr/bin/env python3
"""Reproducibility checks for 'When gold disconnects' (revised).

Part A  brute-force replay of every window X <= LIM: verifies
        (i)  #gold components == #classes of present 2-power doors  (Theorem 4)
        (ii) gold is disconnected on all of [r0(M), 2 r0(M) - 2]     (Theorem 9)
Part B  exact M31 computation: owners, hire times, first arc window X1 (Theorem 12).
Requires: python3, sympy.  Run with ordinary assertions enabled.
"""
import sys
from bisect import bisect_left, bisect_right
from sympy import isprime, factorint

LIM = int(sys.argv[1]) if len(sys.argv) > 1 else 10**6

def m0(p):                       # 3-free door: p + chi_3(p)
    return p + 1 if p % 3 == 1 else p - 1

# ---------- Part A ----------
spf = list(range(LIM + 3))
for i in range(2, int((LIM + 2) ** 0.5) + 1):
    if spf[i] == i:
        for j in range(i * i, LIM + 3, i):
            if spf[j] == j:
                spf[j] = i

def oddfac(n):
    while n % 2 == 0:
        n //= 2
    out = set()
    while n > 1:
        f = spf[n]; out.add(f)
        while n % f == 0:
            n //= f
    return out

is_sink = lambda q: not oddfac(m0(q))      # door is a power of 2
par, S, first_owner = {}, set(), {}
def find(x):
    while par[x] != x:
        par[x] = par[par[x]]; x = par[x]
    return x
def union(a, b):
    a, b = find(a), find(b)
    if a != b:
        par[a] = b; return 1
    return 0

primes = [p for p in range(5, LIM + 1) if spf[p] == p]
cc, present, ccs = 0, [], []
bad = 0
for p in primes:
    new = []
    for q in oddfac(m0(p)):
        if q not in S:
            S.add(q); par[q] = q; cc += 1; first_owner[q] = p; new.append(q)
            if is_sink(q): present.append(q)
    for q in new:                                   # out-arcs of a newly hired vertex
        for r in oddfac(m0(q)):
            assert r in S                           # door closure (Lemma)
            cc -= union(q, r)
    classes = len({find(s) for s in present})
    if cc != classes: bad += 1                      # Theorem 4 (iii)
    ccs.append(cc)
print(f"Part A: windows checked = {len(primes)}, violations of Theorem 4 = {bad}")
assert bad == 0

sinks = sorted(q for q in first_owner if is_sink(q) and q > 5)
for M in sinks:
    r0 = first_owner[M]; hi = min(2 * r0 - 2, LIM)
    i0, i1 = bisect_left(primes, r0), bisect_right(primes, hi)
    ok = all(c >= 2 for c in ccs[i0:i1])
    print(f"  M={M:>8}  r0={r0:>8}  [r0, 2r0-2]=[{r0}, {2*r0-2}]  checked to {hi}: {ok}")
    assert ok

# ---------- Part B ----------
M = 2**31 - 1
is_owner = lambda p, Q: p > 3 and isprime(p) and m0(p) % Q == 0
def owners_upto(Q, top):                   # all owners p <= top (p = tQ -/+ 1, t even)
    return sorted(p for t in range(2, top // Q + 3, 2)
                  for p in (t * Q - 1, t * Q + 1) if p <= top and is_owner(p, Q))
def hire_time(w, bound):                   # least owner of w that is <= bound, else None
    c = [p for t in range(2, bound // w + 3, 2)
         for p in (t * w - 1, t * w + 1) if p <= bound and is_owner(p, w)]
    return min(c) if c else None

r0 = owners_upto(M, 60 * M)[0]
assert r0 == 98784247763 == 46 * M + 1 and isprime(r0)
print("Part B: r0 =", r0, " m0(r0) =", factorint(m0(r0)), " t =", (r0 - 1) // M)
h0 = hire_time(r0, 10**13)
print("  hire time of r0:", h0, "=", (h0 - 1) // r0, "* r0 + 1")
ows = owners_upto(M, (h0 + 1) // 2)        # only owners with 2w-1 <= h0 can matter
print(f"  owners w of M31 with 2w-1 <= {h0}: {len(ows)}")
best = None
for w in ows:
    hw = hire_time(w, h0)
    print(f"    w={w:>15}  door={factorint(m0(w))}  hire={hw}")
    if hw is not None and (best is None or hw < best[0]): best = (hw, w)
X1, w1 = best
print("  first live arc into M31 at X1 =", X1, " (w =", w1, ", 2w-1 =", 2 * w1 - 1, ")")
assert X1 == 627065224921 and w1 == 313532612461
chain = [73]
while chain[-1] != 5:
    (q,) = [f for f in factorint(m0(chain[-1])) if f > 2]; chain.append(q)
print("  mainland chain from 73:", " -> ".join(map(str, chain)))
