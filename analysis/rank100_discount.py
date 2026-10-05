#!/usr/bin/env python3
"""Discount sieve for rank-100 owner floors.

Never builds the 3.89-million-digit N. Never calls PFGW.

    N = k*q + ε = (2293*k)*2^12918431 + (ε - k)

For each odd prime r ≤ B:

    t = q mod r = 2293*2^EXP - 1 mod r

When t ≠ 0, divisibility selects two multiplier classes:

    k ≡  t⁻¹ (mod r)   for ε=-1
    k ≡ -t⁻¹ (mod r)   for ε=+1

The sieve intersects those classes with k ≡ 2 or 4 (mod 6) and marks whole
arithmetic progressions. It never builds the 3.89-million-digit candidates.

Leave the Xeon walker alone (k=206 Fermat). This is the cheap filter
that should have run before PFGW ever saw a 0.28 s joke.

    python3 rank100_discount.py --selftest
    python3 rank100_discount.py --verify-floors rank100-floors/floors.jsonl
    python3 rank100_discount.py --B 100000000 --max-k 400 --out rank100-discount

Resumes from discount.jsonl. Ctrl-C is safe.
"""
from __future__ import annotations

import argparse, json, sys, time
from collections import Counter
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


def first_in_progression(start: int, residue: int, modulus: int) -> int:
    """Smallest n >= start with n ≡ residue (mod modulus)."""
    return start + ((residue - start) % modulus)


def crt_coprime(a: int, m: int, b: int, n: int) -> int:
    """Residue modulo m*n for x ≡ a (mod m), x ≡ b (mod n), gcd(m,n)=1."""
    inv_m = pow(m, -1, n)
    return (a + m * (((b - a) * inv_m) % n)) % (m * n)


def killed_by_factor(k: int, factor: int) -> bool:
    """Check factor | k*q+eps(k) without constructing q or N."""
    if factor <= 1:
        return False
    q_mod = (A0 * pow(2, EXP, factor) - 1) % factor
    return (k * q_mod + eps(k)) % factor == 0


def verify_floors(path: Path) -> int:
    """Audit a PFGW floors.jsonl file using only modular arithmetic."""
    rows = []
    for lineno, line in enumerate(path.read_text().splitlines(), 1):
        if not line.strip():
            continue
        row = json.loads(line)
        row["_lineno"] = lineno
        rows.append(row)

    counts: Counter[str] = Counter()
    bad = 0
    for row in rows:
        k = int(row["k"])
        status = row.get("status", "unknown")
        factors = [int(x) for x in row.get("factors", []) if str(x).isdigit()]
        if factors:
            ok = all(killed_by_factor(k, f) for f in factors)
            if ok:
                counts["explicit_factor_verified"] += 1
            else:
                bad += 1
                counts["explicit_factor_failed"] += 1
                print(
                    f"BAD factor witness line={row['_lineno']} k={k} "
                    f"factors={factors}",
                    file=sys.stderr,
                )
        elif status == "composite":
            if float(row.get("seconds", 0)) >= 3600:
                counts["fermat_composite_no_factor"] += 1
            else:
                counts["composite_no_factor"] += 1
        elif status == "unknown" and float(row.get("seconds", 0)) >= 3600:
            counts["fermat_composite_no_factor"] += 1
        elif status in ("prp", "prime"):
            counts[status] += 1
        else:
            counts[status] += 1

    print(f"rows={len(rows)} file={path}")
    for key in sorted(counts):
        print(f"{key}={counts[key]}")
    return 1 if bad else 0


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
    ap.add_argument("--verify-floors", type=Path, help="verify stored PFGW factor witnesses")
    args = ap.parse_args()
    if args.selftest:
        return selftest()
    if args.verify_floors:
        return verify_floors(args.verify_floors)
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

    # alive = k still unkilled; fac records the first trial prime found.
    alive = set(ks)
    fac = {}
    t1 = time.monotonic()
    n = len(primes)
    for i, p in enumerate(primes, 1):
        r = pow(2, EXP, p)
        t = (A0 * r - 1) % p
        if t != 0:
            if p == 3:
                # Tiny non-coprime CRT case; not worth special machinery.
                for k in tuple(alive):
                    if (k * t + eps(k)) % p == 0:
                        alive.remove(k)
                        fac[k] = p
            else:
                inv_t = pow(t, -1, p)
                # ε=-1 branch: k ≡ t⁻¹ (mod p), k ≡ 2 (mod 6).
                # ε=+1 branch: k ≡ -t⁻¹ (mod p), k ≡ 4 (mod 6).
                for residue_p, residue_6 in ((inv_t, 2), ((-inv_t) % p, 4)):
                    residue = crt_coprime(residue_p, p, residue_6, 6)
                    step = 6 * p
                    k = first_in_progression(args.start_k, residue, step)
                    while k <= args.max_k:
                        if k in alive:
                            alive.remove(k)
                            fac[k] = p
                        k += step
        if i == n or i % 50_000 == 0:
            print(
                f"  p={p}  {i}/{n}  unkilled {len(alive)}/{len(ks)}  "
                f"{time.monotonic() - t1:.1f}s",
                flush=True,
            )

    now = time.monotonic()
    with dst.open("a") as out, survivors.open("a") as surv:
        for k in ks:
            e = eps(k)
            if k not in alive:
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

    n_kill = sum(1 for k in ks if k not in alive)
    n_surv = len(ks) - n_kill
    print(
        f"done killed={n_kill} survivors={n_surv}  {time.monotonic() - t0:.1f}s  "
        f"B={args.B}  -> {dst}",
        flush=True,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
