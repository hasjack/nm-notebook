# Thin hire-rate table H(X), R(X)

## Definitions

- $m_0(p)=p+\chi_3(p)$ with $\chi_3(p)=+1$ if $p\equiv1\pmod{3}$, else $-1$ if $p\equiv2\pmod{3}$ (even, 3-free).
- Owners: odd primes $5\le p\le X$ (hub $2$ separate).
- Odd prime $q\ne3$ is hired by $X$ if $q\mid m_0(p)$ for some owner $p\le X$.
- $H(X)$ = number of distinct odd hired primes by $X$ ($=|S_X|-1$ if $S_X$ includes 2).
- $R(X)=H(X)\,(\ln X)^2/(X\,\ln\ln X)$ (natural logs).

## Method

Owner-ordered segmented rem-sieve implemented in C (`hire_rate_HX_core.c`, gcc -O3 -march=native) and wrapped by `hire_rate_HX.py`. Segment size $2^{22}$. For each owner window $[A,B)$, build a `uint64` rem array on $m_0\in[A-1,B]$, divide out all prime factors $\le\sqrt{B}$, then factor each owner's $m_0$ via small primes + rem leftover. Hired flags live in a bitset over odd integers ($\approx X/16$ bytes — no full SPF of size $X$). Single pass to $X_{\max}=2\cdot10^{10}$ with checkpoint snapshots after all owners $p\le X$ are processed. Pure-Python twin: `python3 hire_rate_HX.py --python` (same algorithm; verified through $10^8$).

Peak RSS ≈ 634 MB at $X=2\cdot10^{10}$. Total wall ≈ 964.73s.

## Sanity

Exact matches to known checkpoints:

| X | H(X) listed | H(X) computed |
| ---: | ---: | ---: |
| 10000 | 361 | 361 |
| 500000 | 9291 | 9291 |
| 10000000 | 125661 | 125661 |
| 100000000 | 980292 | 980292 |
| 1000000000 | 7877140 | 7877140 |
| 2200000000 | 16173662 | 16173662 |

## Table

| X | H(X) | R(X) | wall_s |
| ---: | ---: | ---: | ---: |
| 10000 | 361 | 1.379246 | 0.12 |
| 100000 | 2401 | 1.302436 | 0.12 |
| 500000 | 9291 | 1.242952 | 0.12 |
| 1000000 | 16688 | 1.213048 | 0.13 |
| 5000000 | 68222 | 1.186555 | 0.26 |
| 10000000 | 125661 | 1.174335 | 0.40 |
| 50000000 | 527157 | 1.152420 | 1.69 |
| 100000000 | 980292 | 1.141710 | 3.44 |
| 500000000 | 4195019 | 1.123078 | 18.37 |
| 1000000000 | 7877140 | 1.115995 | 38.26 |
| 2200000000 | 16173662 | 1.108654 | 88.72 |
| 5000000000 | 34296996 | 1.101438 | 213.73 |
| 10000000000 | 64838984 | 1.095989 | 452.45 |
| 15000000000 | 94178863 | 1.092908 | 703.97 |
| 20000000000 | 122776796 | 1.090762 | 964.73 |
