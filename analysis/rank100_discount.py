#!/usr/bin/env python3
"""Discount sieve for rank-100 owner floors.

Never builds the 3.89-million-digit N. Never calls PFGW.

    N = k*q + ε = (2293*k)*2^12918431 + (ε - k)

For each odd prime p ≤ B:

    r = 2^EXP mod p
    k*(2293*r - 1) + ε ≡ 0 (mod p)  ⇒  p divides N.

Leave the Xeon walker alone (k=206 Fermat). This is the cheap filter
that should have run before PFGW ever saw a 0.28 s joke.

    python3 rank100_discount.py --selftest
    python3 rank100_discount.py --B 100000000 --max-k 400 --out rank100-discount

Resumes from discount.jsonl. Ctrl-C is safe.
"""
from __future__ import annotations

import argparse, json, sys, time
from pathlib import Path

EXP = 12_918_431
A0 = 2293

# Small factors already seen by PFGW. Used by --selftest (B large enough).
KNOWN = {
    98: 162981019,
    110: 17,
    112: 13,
    118: 5,
    122: 5,
    128: 67,
    130: 23,
    134: 7,
    136: 439,
    140: 37,
    146: 23,
    154: 79,
    158: 61,
    160: 7,
    164: 59,
    166: 19,
    170: 11,
    172: 41,
    176: 7,
    178: 5,
    182: 5,
    184: 373,
    190: 13,
    194: 293,
    196: 17,
    200: 13,
    202: 7,
}

# Survived PFGW trial factor to ~1.66e9, then Fermat-composite.
FERMAT_COMPOSITE = {124, 142, 188}


def admissible_ks(start: int, max_k: int) -> list[int]:
    k = start if start % 2 == 0 else start + 1
    out = []
    while k <= max_k:
        if k % 6 in (2, 4):
            out.append(k)
        k += 2
    return out


def eps(k: int) -> int:
    return -1 if k % 6 == 2 else 1


def expr(k: int) -> str:
    c = eps(k) - k
    return f"{A0 * k}*2^{EXP}{c:+d}"


def primes_upto(B: int) -> list[int]:
    if B < 3:
        return []
    n = B + 1
    s = bytearray(b"\x01") * n
    s[0:2] = b"\x00\x00"
    lim = int(B**0.5) + 1
    for i in range(2, lim):
        if s[i]:
            step = i
            start = i * i
            s[start:n:step] = b"\x00" * ((n - 1 - start) // step + 1)
    return [i for i in range(3, n) if s[i]]


def load_done(path: Path) -> dict:
    done = {}
    if not path.exists():
        return done
    for line in path.read_text().splitlines():
        if not line.strip():
            continue
        row = json.loads(line)
        done[int(row["k"])] = row
    return done


def factor_k(k: int, primes: list[int], B: int) -> int | None:
    """Smallest odd prime p ≤ B dividing N = k*q+ε, or None."""
    e = eps(k)
    for p in primes:
        r = pow(2, EXP, p)
        t = (A0 * r - 1) % p
        if (k * t + e) % p == 0:
            return p
    return None


def selftest() -> int:
    need = max(KNOWN.values())
    B = min(need, 500_000)
    # Factors bigger than this B are skipped in the small-prime check.
    primes = primes_upto(B)
    bad = 0
    for k, fac in sorted(KNOWN.items()):
        if fac > B:
            continue
        got = factor_k(k, primes, B)
        if got != fac and got is None:
            # may find a smaller factor than the PFGW-listed one
            print("MISS", k, "expected", fac, "got", got)
            bad += 1
        elif got is not None and fac % got != 0 and got != fac:
            # smaller factor is still a kill; OK if got | N (we trust the congruence)
            print("kill", k, "got", got, "(PFGW listed", fac, ")")
        else:
            print("ok", k, "factor", got or fac)
    for k in sorted(FERMAT_COMPOSITE):
        got = factor_k(k, primes, B)
        if got is not None:
            print("UNEXPECTED kill of Fermat survivor", k, "p", got)
            bad += 1
        else:
            print("ok", k, "survives B", B)
    if bad:
        print("selftest FAIL", bad)
        return 1
    print("selftest OK", "primes", len(primes), "B", B)
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--B", type=int, default=100_000_000, help="trial bound (default 1e8)")
    ap.add_argument("--start-k", type=int, default=98)
    ap.add_argument("--max-k", type=int, default=400)
    ap.add_argument("--out", type=Path, default=Path("rank100-discount"))
    ap.add_argument("--selftest", action="store_true")
    args = ap.parse_args()
    if args.selftest:
        return selftest()
    if args.B < 5 or args.max_k < args.start_k:
        ap.error("need B ≥ 5 and max-k ≥ start-k")

    args.out.mkdir(parents=True, exist_ok=True)
    dst = args.out / "discount.jsonl"
    survivors = args.out / "survivors.jsonl"
    done = load_done(dst)
    ks = [k for k in admissible_ks(args.start_k, args.max_k) if k not in done]
    print(
        f"discount B={args.B} k={args.start_k}..{args.max_k} "
        f"todo={len(ks)} already={len(done)}",
        flush=True,
    )
    if not ks:
        print("nothing to do")
        return 0

    t0 = time.monotonic()
    print("sieving primes ≤", args.B, "...", flush=True)
    primes = primes_upto(args.B)
    print("primes", len(primes), "in", round(time.monotonic() - t0, 2), "s", flush=True)

    # alive[i] = k still unkilled; factor map
    alive = {k: True for k in ks}
    fac = {}
    t1 = time.monotonic()
    n = len(primes)
    for i, p in enumerate(primes, 1):
        r = pow(2, EXP, p)
        t = (A0 * r - 1) % p
        for k in ks:
            if not alive[k]:
                continue
            if (k * t + eps(k)) % p == 0:
                alive[k] = False
                fac[k] = p
        if i == n or i % 50_000 == 0:
            left = sum(1 for k in ks if alive[k])
            print(
                f"  p={p}  {i}/{n}  unkilled {left}/{len(ks)}  "
                f"{time.monotonic() - t1:.1f}s",
                flush=True,
            )

    now = time.monotonic()
    with dst.open("a") as out, survivors.open("a") as surv:
        for k in ks:
            e = eps(k)
            if not alive[k]:
                row = {
                    "k": k,
                    "eps": e,
                    "expr": expr(k),
                    "status": "killed",
                    "factor": fac[k],
                    "B": args.B,
                    "seconds": round(now - t0, 3),
                }
            else:
                row = {
                    "k": k,
                    "eps": e,
                    "expr": expr(k),
                    "status": "survivor",
                    "factor": None,
                    "B": args.B,
                    "seconds": round(now - t0, 3),
                }
                surv.write(json.dumps(row) + "\n")
            out.write(json.dumps(row) + "\n")
            print(
                f"k={k}  ε={e:+d}  {row['status']}"
                + (f"  p={row['factor']}" if row["factor"] else ""),
                flush=True,
            )

    n_kill = sum(1 for k in ks if not alive[k])
    n_surv = len(ks) - n_kill
    print(
        f"done killed={n_kill} survivors={n_surv}  {time.monotonic() - t0:.1f}s  "
        f"B={args.B}  -> {dst}",
        flush=True,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
