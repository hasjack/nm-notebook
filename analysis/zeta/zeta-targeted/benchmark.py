#!/usr/bin/env python3
"""Time one plus-side candidate: generation, PRP, sample Pocklington.

    python3 benchmark.py --family wide --vmin2 2 --vmax2 2 \\
      --nmin 10 --nmax 10 --pool-max 71 \\
      --min-digits 100000 --max-digits 130000 --cert-witnesses 3
"""
import argparse, json, math, sys, time
from pathlib import Path
import hunt

sys.set_int_max_str_digits(0)

def time_witnesses(q, factors, n):
    """Time n Pocklington witnesses; return (seconds, n_ok, n_factors)."""
    primes = list(factors)
    n = min(n, len(primes))
    t0 = time.monotonic()
    ok = 0
    for p in primes[:n]:
        found = False
        for a in range(2, 502):
            if hunt.modpow(a, q - 1, q) == 1 and math.gcd(
                hunt.modpow(a, (q - 1) // p, q) - 1, q
            ) == 1:
                found = True
                break
        if found:
            ok += 1
        else:
            break
    return time.monotonic() - t0, ok, len(primes)

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--family", choices=("tight", "wide"), default="wide")
    ap.add_argument("--vmin2", type=int, default=2)
    ap.add_argument("--vmax2", type=int, default=2)
    ap.add_argument("--nmin", type=int, default=10)
    ap.add_argument("--nmax", type=int, default=10)
    ap.add_argument("--emin", type=int, default=2)
    ap.add_argument("--emax", type=int, default=2)
    ap.add_argument("--pool-max", type=int, default=71)
    ap.add_argument("--min-digits", type=int, default=100000)
    ap.add_argument("--max-digits", type=int, default=130000)
    ap.add_argument("--seed", type=int, default=20260923)
    ap.add_argument("--attempts", type=int, default=200)
    ap.add_argument("--cert-witnesses", type=int, default=3)
    ap.add_argument("--out", type=Path, default=None)
    args = ap.parse_args()
    force = 2 if args.family == "tight" else None
    pool = hunt.odd_primes_upto(args.pool_max)
    small = [p for p in range(5, 10000) if hunt.prime64(p)]
    report = {
        "attempts": 0,
        "in_band": 0,
        "plus_side_in_band": 0,
        "sieved": 0,
        "prp_composite": 0,
        "stages": [],
    }
    survivor = None
    for i in range(args.attempts):
        f = hunt.index_for(
            i, args.seed, pool, args.nmin, args.nmax, args.emin, args.emax,
            args.vmin2, args.vmax2, force,
        )
        t0 = time.monotonic()
        k, d, df = hunt.denominator(f)
        gen = time.monotonic() - t0
        q = d + (1 if d % 3 == 1 else -1)
        digits = int(q.bit_length() * math.log10(2)) + 1
        plus = q == d + 1
        report["attempts"] += 1
        row = {
            "attempt": i,
            "k_mod12": k % 12,
            "v2": f.get(2),
            "digits": digits,
            "plus": plus,
            "generation_seconds": round(gen, 4),
            "tau": hunt.divisor_count(f),
            "n_vStaudt": len(df),
        }
        if not args.min_digits <= digits <= args.max_digits:
            row["status"] = "outside-digit-band"
            report["stages"].append(row)
            continue
        report["in_band"] += 1
        if not plus:
            row["status"] = "minus-side"
            report["stages"].append(row)
            print("in-band minus", digits, "digits  gen", round(gen, 3), "s", flush=True)
            continue
        report["plus_side_in_band"] += 1
        t1 = time.monotonic()
        divisor = next((p for p in small if q != p and q % p == 0), None)
        sieve = time.monotonic() - t1
        row["sieve_seconds"] = round(sieve, 4)
        if divisor:
            row["status"] = "sieved-composite"
            report["sieved"] += 1
            report["stages"].append(row)
            print("plus sieved", digits, "digits  gen", round(gen, 3), "s", flush=True)
            continue
        print("PRP start", digits, "digits  gen", round(gen, 3), "s", flush=True)
        t2 = time.monotonic()
        prime = hunt.is_prime(q)
        prp = time.monotonic() - t2
        row["prp_seconds"] = round(prp, 3)
        if not prime:
            row["status"] = "mr-composite"
            report["prp_composite"] += 1
            report["stages"].append(row)
            print("PRP composite", digits, "digits in", round(prp, 2), "s", flush=True)
            continue
        row["status"] = "probable"
        row["index"] = str(k)
        if args.cert_witnesses > 0:
            print(
                "PRP hit", digits, "digits in", round(prp, 2), "s; sampling",
                args.cert_witnesses, "witnesses", flush=True,
            )
            tw, ok, nfac = time_witnesses(q, df, args.cert_witnesses)
            row["cert_sample_seconds"] = round(tw, 3)
            row["cert_sample_n"] = ok
            row["n_factors"] = nfac
            if ok:
                row["cert_extrapolated_seconds"] = round(tw / ok * nfac, 1)
        survivor = row
        report["stages"].append(row)
        report["survivor"] = {
            k: row[k]
            for k in row
            if k != "index"
        }
        report["survivor"]["index_digits"] = len(str(k))
        break
    else:
        report["status"] = "no-survivor"
    text = json.dumps(report, indent=2)
    print(text)
    if args.out:
        args.out.write_text(text)

if __name__ == "__main__":
    main()
