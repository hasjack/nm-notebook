#!/usr/bin/env python3
"""One-shot best-practice verify for the thin M31 corridor integers.

Ascending compute:
  0) Hand door / X* arithmetic (+ optional gp isprime/cert)
  1) thin_owners.py 31
  2) M31_mixed_connectors.py
  3) thin_owner_of_q.py for tau(v)

Usage (from this directory):
  python3 verify_best_practice.py
  python3 verify_best_practice.py --gp          # also call gp for primality
  python3 verify_best_practice.py --skip-mixed  # skip the longer mixed scan
  python3 verify_best_practice.py --skip-tau-v  # skip the heaviest hunt

Requires: python3. Optional: gp (PARI) on PATH for --gp.
"""
from __future__ import annotations

import argparse
import shutil
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent

# Expected corridor integers (notes / Islands)
XSTAR = 92_274_421
BRIDGE = 46_137_211
R0 = 98_784_247_763
V = 300_647_710_579
TAU_V = 24_051_816_846_319
P_STAR = 313_532_612_461
TAU_P_STAR = 627_065_224_921
M31 = (1 << 31) - 1


def chi3(p: int) -> int:
    return 1 if p % 3 == 1 else -1


def m0(p: int) -> int:
    return p + chi3(p)


def ok(msg: str) -> None:
    print(f"  PASS  {msg}")


def bad(msg: str) -> None:
    print(f"  FAIL  {msg}")


def gp_run(code: str, timeout: int = 120) -> str | None:
    """Run a GP snippet via stdin. Homebrew PARI 2.17+ has no -c flag."""
    gp = shutil.which("gp")
    if not gp:
        return None
    payload = code.rstrip() + '\n'
    if not payload.rstrip().endswith("quit"):
        payload = payload + "quit" + '\n'
    r = subprocess.run(
        [gp, "-q", "-f"],
        input=payload,
        capture_output=True,
        text=True,
        timeout=timeout,
    )
    if r.returncode != 0:
        return None
    return r.stdout


def gp_isprime(n: int) -> bool | None:
    # quiet one-shot; 1 = prime, 0 = composite
    out = gp_run(f"print(isprime({n}));")
    if out is None:
        return None
    line = out.strip().splitlines()[-1].strip() if out.strip() else ""
    if line == "1":
        return True
    if line == "0":
        return False
    return None


def gp_cert(n: int) -> bool:
    """Return True if gp can certify n prime (primecert)."""
    out = gp_run(
        f'c=primecert({n}); print(type(c)!="t_INT" || c!=0);',
        timeout=600,
    )
    if out is None:
        return False
    line = out.strip().splitlines()[-1].strip() if out.strip() else ""
    return line in ("1", "true", "True")



def step0_hand(use_gp: bool) -> bool:
    print("\n=== 0. Hand checks (X* + doors) ===")
    passed = True

    m_x = m0(XSTAR)
    if m_x == 2 * BRIDGE:
        ok(f"m0(X*)={m_x} = 2·{BRIDGE}")
    else:
        bad(f"m0(X*)={m_x}, expected {2 * BRIDGE}")
        passed = False

    m_b = m0(BRIDGE)
    # 2^2 · 11 · 1048573
    if m_b == 4 * 11 * 1_048_573:
        ok(f"m0(bridge)={m_b} = 2²·11·1048573")
    else:
        bad(f"m0(bridge)={m_b}")
        passed = False

    if m0(R0) // M31 == 46 and m0(R0) % M31 == 0:
        ok(f"m0(r0)/M31=46")
    else:
        bad(f"m0(r0)/M31={m0(R0) // M31 if m0(R0) % M31 == 0 else 'n/a'}")
        passed = False

    if m0(P_STAR) // M31 == 146 and m0(P_STAR) % M31 == 0:
        ok(f"m0(p*)/M31=146=2·73")
    else:
        bad(f"m0(p*)/M31 check failed")
        passed = False

    if m0(V) == 4 * 5 * 7 * M31:
        ok(f"m0(v)=2²·5·7·M31")
    else:
        bad(f"m0(v)={m0(V)}, expected {4 * 5 * 7 * M31}")
        passed = False

    if TAU_P_STAR == 2 * P_STAR - 1:
        ok(f"τ(p*)=2p*-1 (tight floor)")
    else:
        bad(f"τ(p*)={TAU_P_STAR} ≠ 2p*-1={2 * P_STAR - 1}")
        passed = False

    primes = {
        "X*": XSTAR,
        "bridge": BRIDGE,
        "r0": R0,
        "v": V,
        "τ(v)": TAU_V,
        "p*": P_STAR,
        "M31": M31,
    }
    if use_gp:
        print("  --- gp isprime / primecert ---")
        if not shutil.which("gp"):
            bad("gp not on PATH (install PARI/GP or drop --gp)")
            passed = False
        else:
            for name, n in primes.items():
                ip = gp_isprime(n)
                if ip is True:
                    ok(f"gp isprime({name})={n}")
                elif ip is False:
                    bad(f"gp says composite: {name}={n}")
                    passed = False
                else:
                    bad(f"gp isprime failed for {name}")
                    passed = False
            # Cert the big corridor primes (skip tiny ones if slow policy — cert all named)
            for name in ("r0", "v", "τ(v)", "p*"):
                n = primes[name]
                print(f"    certifying {name}={n} …", flush=True)
                if gp_cert(n):
                    ok(f"gp primecert({name})")
                else:
                    bad(f"gp primecert failed for {name}")
                    passed = False
    else:
        print("  (tip: re-run with --gp to certify primes via PARI)")

    return passed


def run_script(args: list[str], expect_substr: list[str], label: str) -> bool:
    print(f"\n=== {label} ===")
    print(f"  $ {' '.join(args)}", flush=True)
    t0 = time.perf_counter()
    r = subprocess.run(args, cwd=str(HERE), capture_output=True, text=True)
    wall = time.perf_counter() - t0
    sys.stdout.write(r.stdout)
    if r.stderr:
        sys.stderr.write(r.stderr)
    if r.returncode != 0:
        bad(f"exit {r.returncode} after {wall:.2f}s")
        return False
    out = r.stdout
    passed = True
    for s in expect_substr:
        if s in out:
            ok(f"found {s}")
        else:
            bad(f"missing expected `{s}` in output")
            passed = False
    print(f"  wall {wall:.2f}s")
    return passed


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--gp", action="store_true", help="use gp isprime + primecert")
    ap.add_argument("--skip-mixed", action="store_true")
    ap.add_argument("--skip-tau-v", action="store_true")
    args = ap.parse_args()

    print("Hire thin verify — best practice (ascending)")
    print(f"cwd scripts: {HERE}")

    results = []
    results.append(("0 hand", step0_hand(args.gp)))

    py = sys.executable
    results.append(
        (
            "1 r0",
            run_script(
                [py, "thin_owners.py", "31", "--count", "5"],
                [f"Smallest owner: {R0}", str(R0)],
                "1. thin_owners.py 31  →  r0",
            ),
        )
    )

    if not args.skip_mixed:
        results.append(
            (
                "2 mixed",
                run_script(
                    [py, "M31_mixed_connectors.py"],
                    [
                        f"EARLIEST mixed τ found: {TAU_P_STAR}",
                        f"via owner p={P_STAR}",
                        str(P_STAR),
                        str(TAU_P_STAR),
                    ],
                    "2. M31_mixed_connectors.py  →  p*, τ(p*)",
                ),
            )
        )
    else:
        print("\n=== 2. mixed scan SKIPPED (--skip-mixed) ===")

    if not args.skip_tau_v:
        results.append(
            (
                "3 tau(v)",
                run_script(
                    [py, "thin_owner_of_q.py", str(V), "--count", "3"],
                    [f"Smallest owner: {TAU_V}", str(TAU_V)],
                    "3. thin_owner_of_q.py v  →  τ(v)",
                ),
            )
        )
    else:
        print("\n=== 3. τ(v) SKIPPED (--skip-tau-v) ===")

    print("\n" + "=" * 60)
    print("SUMMARY")
    all_ok = True
    for name, p in results:
        print(f"  {'PASS' if p else 'FAIL'}  {name}")
        all_ok = all_ok and p
    print("=" * 60)
    if all_ok:
        print("All requested checks matched the note integers.")
        return 0
    print("Mismatch — freeze Islands rail until reconciled.")
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
