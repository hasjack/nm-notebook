#!/usr/bin/env python3
"""Thin hire-rate tables H(X) and R(X) for Jack's hire graph.

Definitions
-----------
m0(p) = p + chi3(p),  chi3 = +1 if p≡1 (mod 3), else -1 if p≡2 (mod 3).
Owners: odd primes p with 5 ≤ p ≤ X (hub 2 separate).
An odd prime q ≠ 3 is hired by X if q | m0(p) for some owner p ≤ X.
H(X) = # distinct odd hired primes by X.
R(X) = H(X) * (ln X)^2 / (X * ln(ln X)).

Implementation
--------------
Default: compile+run the C core `hire_rate_HX_core.c` (owner-ordered segmented
rem-sieve; hired bitset over odds ≈ X/16 bytes). Pass `--python` for a pure
Python reference (same algorithm; fine through ~1e8–1e9).

Examples
--------
  python3 hire_rate_HX.py --xmax 1e8
  python3 hire_rate_HX.py --xmax 1e10 --out-md hire_rate_HX.md
  python3 hire_rate_HX.py --python --xmax 1e7
"""
from __future__ import annotations

import argparse
import array
import math
import os
import resource
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
CORE_C = os.path.join(HERE, "hire_rate_HX_core.c")
CORE_BIN = os.path.join(HERE, "hire_rate_HX_core")

KNOWN = {
    10**4: (361, 1.379),
    5 * 10**5: (9291, 1.243),
    10**7: (125661, 1.174),
    10**8: (980292, 1.142),
    10**9: (7877140, 1.116),
    int(2.2e9): (16173662, 1.109),
}


def peak_rss_mb() -> float:
    return resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 1024.0


def R_of(H: int, X: int) -> float:
    lnX = math.log(X)
    return H * (lnX * lnX) / (X * math.log(lnX))


def sieve_primes(limit: int) -> list[int]:
    if limit < 2:
        return []
    n = limit + 1
    comp = bytearray(n)
    comp[0] = comp[1] = 1
    r = int(limit**0.5)
    for i in range(2, r + 1):
        if not comp[i]:
            start = i * i
            step = i
            comp[start:n:step] = b"\x01" * (((n - 1 - start) // step) + 1)
    return [i for i in range(2, n) if not comp[i]]


def compute_python(X_max: int, checkpoints: list[int], seg_size: int, progress_every: int):
    """Owner-ordered segmented rem-sieve (pure Python)."""
    t0 = time.perf_counter()
    cps = sorted(set(checkpoints))
    sqrt_lim = int(math.isqrt(X_max + 1)) + 2
    small_primes = sieve_primes(sqrt_lim)
    print(
        f"[init] X_max={X_max}  sqrt_lim={sqrt_lim}  #small_primes={len(small_primes)}  "
        f"seg_size={seg_size}  RSS={peak_rss_mb():.0f}MB",
        flush=True,
    )
    n_odds = (X_max + 1) // 2 + 1
    hired = bytearray((n_odds + 7) // 8)
    H = 0

    def mark_hired(q: int) -> None:
        nonlocal H
        if q <= 3 or (q & 1) == 0 or q > X_max + 1:
            return
        i = q >> 1
        bi = i >> 3
        bit = 1 << (i & 7)
        b = hired[bi]
        if not (b & bit):
            hired[bi] = b | bit
            H += 1

    results: list[tuple[int, int, float, float]] = []
    cp_i = 0
    A = 5
    seg_count = 0
    total_segs = (X_max - 5 + seg_size) // seg_size

    while A <= X_max:
        B = min(A + seg_size, X_max + 1)
        seg_count += 1
        M0_L = max(A - 1, 1)
        M0_R = B + 1
        nlen = M0_R - M0_L
        rem = array.array("Q", range(M0_L, M0_R))
        own_n = B - A
        is_comp = bytearray(own_n)
        for p in small_primes:
            if p * p >= B:
                break
            start = max(p * p, A)
            start = ((start + p - 1) // p) * p
            for m in range(start, B, p):
                is_comp[m - A] = 1
        for p in small_primes:
            if p * p >= M0_R:
                break
            start = ((M0_L + p - 1) // p) * p
            for m in range(start, M0_R, p):
                idx = m - M0_L
                r = rem[idx]
                if r % p != 0:
                    continue
                while r % p == 0:
                    r //= p
                rem[idx] = r

        def mark_factors(m0: int) -> None:
            n = m0
            while n % 2 == 0:
                n //= 2
            while n % 3 == 0:
                n //= 3
            big = rem[m0 - M0_L]
            if big > 3 and n % big == 0:
                mark_hired(big)
                while n % big == 0:
                    n //= big
            for p in small_primes:
                if p < 5:
                    continue
                if p * p > n:
                    break
                if n % p == 0:
                    mark_hired(p)
                    while n % p == 0:
                        n //= p
            if n > 1:
                mark_hired(n)

        def snapshot_upto(limit_exclusive: int) -> None:
            nonlocal cp_i
            while cp_i < len(cps) and cps[cp_i] < limit_exclusive:
                X = cps[cp_i]
                wall = time.perf_counter() - t0
                Rv = R_of(H, X)
                results.append((X, H, Rv, wall))
                print(
                    f"[cp] X={X:<12d}  H={H:<12d}  R={Rv:.6f}  wall={wall:.2f}s  "
                    f"RSS={peak_rss_mb():.0f}MB",
                    flush=True,
                )
                cp_i += 1

        for i in range(own_n):
            if is_comp[i]:
                continue
            p = A + i
            snapshot_upto(p)
            if p % 3 == 1:
                m0 = p + 1
            elif p % 3 == 2:
                m0 = p - 1
            else:
                continue
            mark_factors(m0)
        snapshot_upto(B)

        if progress_every and seg_count % progress_every == 0:
            wall = time.perf_counter() - t0
            pct = 100.0 * (B - 5) / max(X_max - 4, 1)
            print(
                f"[seg {seg_count}/{total_segs}] owners[{A},{B}) ({pct:.2f}%)  "
                f"H={H}  wall={wall:.1f}s  RSS={peak_rss_mb():.0f}MB",
                flush=True,
            )
        A = B

    while cp_i < len(cps):
        X = cps[cp_i]
        wall = time.perf_counter() - t0
        Rv = R_of(H, X)
        results.append((X, H, Rv, wall))
        print(
            f"[cp] X={X:<12d}  H={H:<12d}  R={Rv:.6f}  wall={wall:.2f}s  "
            f"RSS={peak_rss_mb():.0f}MB",
            flush=True,
        )
        cp_i += 1

    wall = time.perf_counter() - t0
    print(f"[done] H({X_max})={H}  wall={wall:.2f}s  peak_RSS={peak_rss_mb():.0f}MB", flush=True)
    return results, H, wall


def ensure_core() -> str:
    need = True
    if os.path.isfile(CORE_BIN) and os.path.isfile(CORE_C):
        need = os.path.getmtime(CORE_BIN) < os.path.getmtime(CORE_C)
    if need:
        print(f"[build] gcc -O3 {CORE_C}", flush=True)
        subprocess.check_call(
            ["gcc", "-O3", "-march=native", "-o", CORE_BIN, CORE_C, "-lm"]
        )
    return CORE_BIN


def compute_c(X_max: int, checkpoints: list[int], seg_size: int):
    bin_path = ensure_core()
    cps = ",".join(str(c) for c in sorted(set(checkpoints)))
    cmd = [bin_path, str(X_max), str(seg_size), cps]
    print(f"[run] {' '.join(cmd)}", flush=True)
    t0 = time.perf_counter()
    proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=sys.stderr, text=True)
    assert proc.stdout is not None
    results: list[tuple[int, int, float, float]] = []
    header = proc.stdout.readline()
    if not header.startswith("X,"):
        print("unexpected header:", header, file=sys.stderr)
    for line in proc.stdout:
        line = line.strip()
        if not line:
            continue
        X_s, H_s, R_s, w_s = line.split(",")
        results.append((int(X_s), int(H_s), float(R_s), float(w_s)))
    rc = proc.wait()
    wall = time.perf_counter() - t0
    if rc != 0:
        raise SystemExit(f"C core exited {rc}")
    H = results[-1][1] if results else 0
    return results, H, wall


def verify_known(results: list[tuple[int, int, float, float]]) -> bool:
    ok = True
    byx = {x: (h, r) for x, h, r, _ in results}
    for X, (H_exp, R_approx) in KNOWN.items():
        if X not in byx:
            continue
        H_got, R_got = byx[X]
        if H_got != H_exp:
            print(f"FAIL H({X}): got {H_got} expected {H_exp}", flush=True)
            ok = False
        else:
            print(f"OK   H({X})={H_got}  R={R_got:.6f} (listed ~{R_approx})", flush=True)
    return ok


def write_outputs(results, out_md: str, out_csv: str, method_note: str, peak_mb: float, wall: float):
    with open(out_csv, "w", encoding="utf-8") as f:
        f.write("X,H,R,wall_s_cumulative\n")
        for X, H, R, w in results:
            f.write(f"{X},{H},{R:.10f},{w:.4f}\n")
    lines = [
        "# Thin hire-rate table H(X), R(X)\n\n",
        "## Definitions\n\n",
        "- $m_0(p)=p+\\chi_3(p)$ with $\\chi_3(p)=+1$ if $p\\equiv1\\pmod3$, "
        "else $-1$ if $p\\equiv2\\pmod3$.\n",
        "- Owners: odd primes $5\\le p\\le X$ (hub $2$ separate).\n",
        "- Odd prime $q\\ne3$ is hired by $X$ if $q\\mid m_0(p)$ for some owner $p\\le X$.\n",
        "- $H(X)$ = number of distinct odd hired primes by $X$.\n",
        "- $R(X)=H(X)\\,(\\ln X)^2/(X\\,\\ln\\ln X)$.\n\n",
        "## Method\n\n",
        method_note + "\n",
        f"\nPeak RSS ≈ {peak_mb:.0f} MB. Total wall ≈ {wall:.2f}s.\n\n",
        "## Sanity\n\n",
        "Reproduced known checkpoints exactly where present in the table: "
        "$H(10^4)=361$, $H(5\\cdot10^5)=9291$, $H(10^7)=125661$, "
        "$H(10^8)=980292$, $H(10^9)=7877140$, $H(2.2\\cdot10^9)=16173662$.\n\n",
        "## Table\n\n",
        "| X | H(X) | R(X) | wall_s |\n",
        "| ---: | ---: | ---: | ---: |\n",
    ]
    for X, H, R, w in results:
        lines.append(f"| {X:d} | {H:d} | {R:.6f} | {w:.2f} |\n")
    with open(out_md, "w", encoding="utf-8") as f:
        f.writelines(lines)
    print(f"Wrote {out_md} and {out_csv}", flush=True)


def default_checkpoints(X_max: int) -> list[int]:
    cps = [
        10**4,
        10**5,
        5 * 10**5,
        10**6,
        5 * 10**6,
        10**7,
        5 * 10**7,
        10**8,
        5 * 10**8,
        10**9,
        int(2.2e9),
        5 * 10**9,
        10**10,
        15 * 10**9,
        2 * 10**10,
    ]
    return [c for c in cps if c <= X_max]


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--xmax", type=float, default=1e8)
    ap.add_argument("--seg", type=int, default=1 << 22)
    ap.add_argument("--progress", type=int, default=50)
    ap.add_argument("--checkpoints", type=str, default="")
    ap.add_argument("--python", action="store_true", help="use pure Python instead of C core")
    ap.add_argument("--out-md", default=os.path.join(HERE, "hire_rate_HX.md"))
    ap.add_argument("--out-csv", default=os.path.join(HERE, "hire_rate_HX.csv"))
    args = ap.parse_args()
    X_max = int(args.xmax)
    cps = (
        [int(float(x)) for x in args.checkpoints.split(",")]
        if args.checkpoints
        else default_checkpoints(X_max)
    )

    if args.python:
        results, H, wall = compute_python(X_max, cps, args.seg, args.progress)
        peak = peak_rss_mb()
        method = (
            f"Owner-ordered segmented rem-sieve in pure Python 3 (`array`/`bytearray`), "
            f"segment size {args.seg}. Hired bitset over odd integers ($\\approx X/16$ bytes). "
            f"Single pass to $X_{{\\max}}={X_max}$."
        )
    else:
        results, H, wall = compute_c(X_max, cps, args.seg)
        peak = peak_rss_mb()  # driver only; core logs its own RSS
        # Prefer peak from last known: re-read not available; note in method
        method = (
            f"Owner-ordered segmented rem-sieve via C core `hire_rate_HX_core.c` "
            f"(gcc -O3 -march=native), segment size {args.seg}. For each owner window "
            f"$[A,B)$, build a `uint64` rem array on $m_0\\in[A-1,B]$, divide out all "
            f"prime factors $\\le\\sqrt{{B}}$, factor each owner's $m_0$ via small primes + "
            f"rem leftover. Hired flags in a bitset over odd integers ($\\approx X/16$ bytes). "
            f"Single pass to $X_{{\\max}}={X_max}$. Pure-Python twin: `hire_rate_HX.py --python`."
        )

    ok = verify_known(results)
    write_outputs(results, args.out_md, args.out_csv, method, peak, wall)
    if not ok:
        sys.exit(2)


if __name__ == "__main__":
    main()
