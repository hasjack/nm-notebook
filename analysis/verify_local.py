#!/usr/bin/env python3
"""Local best-practice verify for hire-graph lab scripts (ascending).

Runs from analysis/:
  0) corridor hand checks + thin hunts (analysis/corridor/)
  1) hire-rate H(X)/R(X) smoke via Python twin through 1e7
  2) optional: compile+run C hire-rate tools at a small X_max

Usage:
  python3 verify_local.py
  python3 verify_local.py --gp
  python3 verify_local.py --skip-corridor
  python3 verify_local.py --hire-c --xmax 10000000
  python3 verify_local.py --skip-mixed --skip-tau-v

Requires: python3, gcc (for --hire-c). Optional: gp (PARI) for --gp.
"""
from __future__ import annotations

import argparse
import shutil
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
CORRIDOR = HERE / "corridor"
HIRE = HERE / "hire_rate"

H_1E7 = 125661


def ok(msg: str) -> None:
    print(f"  PASS  {msg}")


def bad(msg: str) -> None:
    print(f"  FAIL  {msg}")


def run(args: list[str], cwd: Path, label: str, expect: list[str] | None = None) -> bool:
    print(f"\n=== {label} ===")
    print(f"  $ {' '.join(args)}", flush=True)
    t0 = time.perf_counter()
    r = subprocess.run(args, cwd=str(cwd), capture_output=True, text=True)
    wall = time.perf_counter() - t0
    sys.stdout.write(r.stdout)
    if r.stderr:
        sys.stderr.write(r.stderr)
    if r.returncode != 0:
        bad(f"exit {r.returncode} after {wall:.2f}s")
        return False
    passed = True
    if expect:
        for s in expect:
            if s in r.stdout or s in r.stderr:
                ok(f"found {s}")
            else:
                bad(f"missing expected `{s}`")
                passed = False
    print(f"  wall {wall:.2f}s")
    return passed


def step_corridor(gp: bool, skip_mixed: bool, skip_tau_v: bool) -> bool:
    if not (CORRIDOR / "verify_best_practice.py").exists():
        bad(f"missing {CORRIDOR}/verify_best_practice.py")
        return False
    args = [sys.executable, "verify_best_practice.py"]
    if gp:
        args.append("--gp")
    if skip_mixed:
        args.append("--skip-mixed")
    if skip_tau_v:
        args.append("--skip-tau-v")
    return run(args, CORRIDOR, "0. corridor thin verify")


def step_hire_python(xmax: int) -> bool:
    py = HIRE / "hire_rate_HX.py"
    if not py.exists():
        bad(f"missing {py}")
        return False
    out_md = Path("/tmp/hire_rate_HX_smoke.md")
    out_csv = Path("/tmp/hire_rate_HX_smoke.csv")
    args = [
        sys.executable,
        str(py),
        "--python",
        "--xmax",
        str(xmax),
        "--out-md",
        str(out_md),
        "--out-csv",
        str(out_csv),
    ]
    expect = [str(H_1E7)] if xmax >= 10_000_000 else None
    return run(args, HIRE, f"1. hire_rate_HX.py --python --xmax {xmax}", expect=expect)


def compile_c(src: Path, out: Path) -> bool:
    gcc = shutil.which("gcc")
    if not gcc:
        bad("gcc not on PATH")
        return False
    args = [gcc, "-O3", "-march=native", "-lm", str(src), "-o", str(out)]
    print(f"\n=== compile {src.name} ===")
    print(f"  $ {' '.join(args)}", flush=True)
    r = subprocess.run(args, cwd=str(HIRE), capture_output=True, text=True)
    if r.returncode != 0:
        sys.stderr.write(r.stderr)
        bad(f"gcc failed for {src.name}")
        return False
    ok(f"built {out.name}")
    return True


def step_hire_c(xmax: int) -> bool:
    cores = [
        ("hire_rate_HX_core.c", "hire_rate_HX_core"),
        ("hire_rate_Rpois.c", "hire_rate_Rpois"),
        ("hire_rate_bin_residual.c", "hire_rate_bin_residual"),
        ("hire_rate_lambda_bins.c", "hire_rate_lambda_bins"),
    ]
    all_ok = True
    for src_name, bin_name in cores:
        src = HIRE / src_name
        out = HIRE / bin_name
        if not src.exists():
            bad(f"missing {src}")
            all_ok = False
            continue
        if not compile_c(src, out):
            all_ok = False
            continue
        if bin_name == "hire_rate_HX_core":
            cps = ",".join(str(x) for x in (10_000, 100_000, 1_000_000, xmax) if x <= xmax)
            cmd = [str(out), str(xmax), str(1 << 20), cps]
            expect = [str(H_1E7)] if xmax >= 10_000_000 else None
            if not run(cmd, HIRE, f"2. {bin_name} xmax={xmax}", expect=expect):
                all_ok = False
        elif bin_name == "hire_rate_Rpois":
            ok(f"{bin_name} compiled (full table is canyon-scale; skip run)")
        else:
            smoke_x = min(xmax, 10_000_000)
            cmd = [str(out), str(smoke_x)]
            if not run(cmd, HIRE, f"2. {bin_name} xmax={smoke_x}"):
                all_ok = False
    return all_ok


def main() -> int:
    ap = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    ap.add_argument("--gp", action="store_true", help="corridor: PARI gp isprime/primecert")
    ap.add_argument("--skip-corridor", action="store_true")
    ap.add_argument("--skip-mixed", action="store_true")
    ap.add_argument("--skip-tau-v", action="store_true")
    ap.add_argument("--skip-hire", action="store_true")
    ap.add_argument("--hire-c", action="store_true", help="also compile (+smoke-run) C hire-rate tools")
    ap.add_argument("--xmax", type=int, default=10_000_000, help="hire-rate smoke X_max (default 1e7)")
    args = ap.parse_args()

    print("Hire lab — local verify (ascending)")
    print(f"analysis root: {HERE}")

    results: list[tuple[str, bool]] = []

    if not args.skip_corridor:
        results.append(("corridor", step_corridor(args.gp, args.skip_mixed, args.skip_tau_v)))
    else:
        print("\n=== 0. corridor SKIPPED ===")

    if not args.skip_hire:
        results.append(("hire python", step_hire_python(args.xmax)))
        if args.hire_c:
            results.append(("hire C", step_hire_c(args.xmax)))
    else:
        print("\n=== hire-rate SKIPPED ===")

    print("\n" + "=" * 60)
    print("SUMMARY")
    all_ok = True
    for name, p in results:
        print(f"  {'PASS' if p else 'FAIL'}  {name}")
        all_ok = all_ok and p
    print("=" * 60)
    if all_ok:
        print("All requested local checks passed.")
        return 0
    print("Mismatch — reconcile before trusting Lab Hire numbers.")
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
