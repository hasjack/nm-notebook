#!/usr/bin/env python3
"""
rank100_owner_probe.py

Probe the current first-un-killed owner candidate for the rank-100 prime

    q = 2293 * 2^12918431 - 1

from the owner-floor catalogue at B = 10^7.

For q ≡ 1 (mod 3) and k = 98 ≡ 2 (mod 3), the admissible owner candidate is

    N = 98*q - 1,

because then m0(N) = N + 1 = 98*q.

Default action:
    - build q and N with GMP via gmpy2
    - run a Fermat compositeness test to base 2
    - if base 2 fails, N is CERTIFIED COMPOSITE
    - if base 2 passes, report only "base-2 probable prime"; this is NOT a proof

Optional:
    --bases 2,3,5,7,11
        Try more Fermat bases, stopping at the first compositeness witness.

    --is-prime
        After all requested Fermat bases pass, call gmpy2.is_prime().
        For a ~3.89-million-digit number this can be very expensive.
        A probable-prime result is still not the preferred final proof; use a
        dedicated N+1/Lucas/PFGW-style proof if the candidate survives.

    --dry-run
        Build the number and print metadata, but do not run the huge powmod.

The script never prints the full decimal expansion of N.

Requirements:
    python3 -m pip install gmpy2

Recommended on macOS:
    caffeinate -dimsu python3 rank100_owner_probe.py

This is a serious computation. A single full-size powmod can take a long time.
"""

from __future__ import annotations

import argparse
import json
import math
import os
import sys
import time
from pathlib import Path

try:
    import gmpy2
    from gmpy2 import mpz
except ImportError:
    sys.stderr.write(
        "Missing gmpy2.\n"
        "Install with:\n"
        "  python3 -m pip install gmpy2\n"
        "If pip cannot build it on macOS, first try:\n"
        "  brew install gmp\n"
        "then reinstall gmpy2.\n"
    )
    raise SystemExit(2)


DEFAULT_EXPONENT = 12_918_431
DEFAULT_COEFF = 2_293
DEFAULT_K = 98
DEFAULT_EPS = -1


def parse_bases(text: str) -> list[int]:
    out: list[int] = []
    for part in text.split(","):
        part = part.strip()
        if not part:
            continue
        a = int(part)
        if a < 2:
            raise argparse.ArgumentTypeError("Fermat bases must be >= 2")
        out.append(a)
    if not out:
        raise argparse.ArgumentTypeError("At least one base is required")
    return out


def human_seconds(seconds: float) -> str:
    if seconds < 60:
        return f"{seconds:.1f} s"
    if seconds < 3600:
        return f"{seconds/60:.2f} min"
    if seconds < 86400:
        return f"{seconds/3600:.2f} h"
    return f"{seconds/86400:.2f} d"


def digits_from_logs(coeff: int, exponent: int, k: int) -> tuple[int, int]:
    # q = coeff*2^exponent - 1
    # N ~= k*coeff*2^exponent
    dq = math.floor(math.log10(coeff) + exponent * math.log10(2.0)) + 1
    dn = math.floor(
        math.log10(k * coeff) + exponent * math.log10(2.0)
    ) + 1
    return dq, dn


def main() -> int:
    ap = argparse.ArgumentParser(
        description="Probe the rank-100 owner candidate N = 98*q - 1."
    )
    ap.add_argument("--exponent", type=int, default=DEFAULT_EXPONENT)
    ap.add_argument("--coeff", type=int, default=DEFAULT_COEFF)
    ap.add_argument("--k", type=int, default=DEFAULT_K)
    ap.add_argument("--eps", type=int, choices=(-1, 1), default=DEFAULT_EPS)
    ap.add_argument(
        "--bases",
        type=parse_bases,
        default=parse_bases("2"),
        help="Comma-separated Fermat bases (default: 2)",
    )
    ap.add_argument(
        "--is-prime",
        action="store_true",
        help="If all Fermat bases pass, call gmpy2.is_prime(N, 25).",
    )
    ap.add_argument(
        "--dry-run",
        action="store_true",
        help="Build q and N, print metadata, but do not run a huge powmod.",
    )
    ap.add_argument(
        "--receipt",
        default="rank100_probe_receipt.json",
        help="JSON receipt path (default: rank100_probe_receipt.json)",
    )
    args = ap.parse_args()

    e = args.exponent
    c = args.coeff
    k = args.k
    eps = args.eps

    dq_est, dn_est = digits_from_logs(c, e, k)

    print("Rank-100 owner probe")
    print("====================")
    print(f"q = {c} * 2^{e} - 1")
    print(f"N = {k}*q {eps:+d}")
    print(f"Estimated digits(q): {dq_est:,}")
    print(f"Estimated digits(N): {dn_est:,}")
    print()

    t0 = time.perf_counter()
    q = mpz(c) * (mpz(1) << e) - 1
    n = mpz(k) * q + eps
    build_s = time.perf_counter() - t0

    # Exact cheap consistency checks.
    q_mod3 = int(q % 3)
    n_mod3 = int(n % 3)

    print(f"Built q and N in {human_seconds(build_s)}")
    print(f"bit_length(q): {q.bit_length():,}")
    print(f"bit_length(N): {n.bit_length():,}")
    print(f"q mod 3 = {q_mod3}")
    print(f"N mod 3 = {n_mod3}")

    # For this catalogue entry we expect q ≡ 1 mod 3 and N = kq - 1 ≡ 1 mod 3,
    # hence chi_3(N)=+1 and m0(N)=N+1=kq.
    if q_mod3 != 1:
        print("WARNING: q mod 3 is not 1; re-check the candidate sign.")
    if n_mod3 != 1:
        print("WARNING: N mod 3 is not 1; re-check the candidate sign.")
    if eps == -1 and n + 1 != k * q:
        raise RuntimeError("Internal consistency failure: N+1 != k*q")

    receipt = {
        "q_form": f"{c}*2^{e}-1",
        "candidate_form": f"{k}*q{eps:+d}",
        "exponent": e,
        "coefficient": c,
        "k": k,
        "epsilon": eps,
        "digits_q_est": dq_est,
        "digits_n_est": dn_est,
        "bit_length_q": int(q.bit_length()),
        "bit_length_n": int(n.bit_length()),
        "q_mod_3": q_mod3,
        "n_mod_3": n_mod3,
        "build_seconds": build_s,
        "bases": args.bases,
        "tests": [],
        "status": "not_tested",
    }

    if args.dry_run:
        receipt["status"] = "dry_run"
        Path(args.receipt).write_text(json.dumps(receipt, indent=2))
        print()
        print("Dry run only; no primality/compositeness test started.")
        print(f"Receipt: {args.receipt}")
        return 0

    print()
    print("WARNING: the next step is the expensive one.")
    print("A failed Fermat test is a rigorous compositeness witness.")
    print("A passed Fermat test is NOT a primality proof.")
    print()

    for a in args.bases:
        aa = mpz(a)

        g = gmpy2.gcd(aa, n)
        if g != 1:
            print(f"Base {a}: gcd(base, N) = {g} -> COMPOSITE")
            receipt["tests"].append(
                {
                    "type": "gcd",
                    "base": a,
                    "gcd": str(g),
                    "result": "composite",
                }
            )
            receipt["status"] = "composite"
            Path(args.receipt).write_text(json.dumps(receipt, indent=2))
            print(f"Receipt: {args.receipt}")
            return 0

        print(f"Base {a}: starting Fermat powmod...")
        sys.stdout.flush()
        t1 = time.perf_counter()

        residue = gmpy2.powmod(aa, n - 1, n)

        elapsed = time.perf_counter() - t1
        passed = residue == 1

        test_row = {
            "type": "fermat",
            "base": a,
            "elapsed_seconds": elapsed,
            "result": "pass" if passed else "composite",
        }

        if not passed:
            # Do not dump a ~4-million-digit residue. Record a short checksum.
            # The witness is reproducible from (form, base).
            residue_mod_1e9p7 = int(residue % 1_000_000_007)
            test_row["residue_mod_1000000007"] = residue_mod_1e9p7
            receipt["tests"].append(test_row)
            receipt["status"] = "composite"
            Path(args.receipt).write_text(json.dumps(receipt, indent=2))

            print(
                f"Base {a}: FAIL after {human_seconds(elapsed)} -> "
                "N IS CERTIFIED COMPOSITE."
            )
            print()
            print(
                "This is enough to certify that the k=98 slot is not the "
                "first owner candidate."
            )
            print(
                "Combine this compositeness witness with the existing receipts "
                "for all admissible k<98 to push the owner floor past 98."
            )
            print(f"Receipt: {args.receipt}")
            return 0

        receipt["tests"].append(test_row)
        print(
            f"Base {a}: PASS after {human_seconds(elapsed)} "
            "(probable-prime evidence only)"
        )
        Path(args.receipt).write_text(json.dumps(receipt, indent=2))

    receipt["status"] = "fermat_prp"

    if args.is_prime:
        print()
        print("All requested Fermat bases passed.")
        print("Starting gmpy2.is_prime(N, 25)... this may be very expensive.")
        sys.stdout.flush()
        t2 = time.perf_counter()
        ip = int(gmpy2.is_prime(n, 25))
        elapsed = time.perf_counter() - t2

        # gmpy2 convention: 0=composite, 1=probably prime, 2=definitely prime
        label = {0: "composite", 1: "probably_prime", 2: "definitely_prime"}.get(
            ip, f"unknown_{ip}"
        )
        receipt["is_prime"] = {
            "return_code": ip,
            "label": label,
            "elapsed_seconds": elapsed,
        }
        receipt["status"] = label
        Path(args.receipt).write_text(json.dumps(receipt, indent=2))

        print(f"is_prime returned {ip} ({label}) after {human_seconds(elapsed)}")

        if ip == 1:
            print(
                "Treat this as probable-prime evidence. For a publication-grade "
                "result, follow with a dedicated N+1/Lucas/PFGW-style proof "
                "using N+1 = 98*q."
            )
        elif ip == 2:
            print("gmpy2 reports N as definitely prime.")
        else:
            print("N is composite.")

    else:
        Path(args.receipt).write_text(json.dumps(receipt, indent=2))
        print()
        print("All requested Fermat bases passed.")
        print("Stopping here by design.")
        print(
            "Do NOT call N prime. Re-run with additional bases or --is-prime, "
            "then use a dedicated N+1 proof if it continues to survive."
        )

    print(f"Receipt: {args.receipt}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
