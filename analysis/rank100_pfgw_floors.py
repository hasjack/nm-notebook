#!/usr/bin/env python3
"""Walk admissible owner floors for PrimePages rank 100 using PFGW.

    q = 2293 * 2^12918431 - 1  (Riesel, q ≡ 1 (mod 3))

Admissible k are even and not divisible by 3 (k ≡ 2 or 4 (mod 6)).
Door parity: ε = -1 if k ≡ 2 (mod 6), else +1.
Then N = k*q + ε = (2293*k)*2^12918431 + (ε - k).

k=98 (N=98q-1) has factor 162981019. This script starts at k=100.

    python3 rank100_pfgw_floors.py --pfgw ./pfgw64
    python3 rank100_pfgw_floors.py --pfgw ./pfgw64 --max-k 200

Resumes from --out/floors.jsonl. Stops on PRP (or --keep-going).
Trial factoring is on (-f). Ctrl-C is safe.
"""
from __future__ import annotations

import argparse, json, os, subprocess, sys, time
from pathlib import Path

EXP = 12_918_431
A0 = 2293  # q = A0 * 2^EXP - 1
K_DEAD = 98  # composite: 162981019 | (98q-1)


def admissible_from(start: int):
    k = start if start % 2 == 0 else start + 1
    while True:
        if k % 6 in (2, 4):
            yield k
        k += 2


def eps(k: int) -> int:
    return -1 if k % 6 == 2 else 1


def expr(k: int) -> str:
    c = eps(k) - k
    return f"{A0 * k}*2^{EXP}{c:+d}"


def parse_pfgw(text: str) -> dict:
    t = text.replace("\r", "\n")
    low = t.lower()
    factors = []
    for line in t.splitlines():
        if "has factors:" in line.lower() or "trivially factors as:" in line.lower():
            rhs = line.split(":", 1)[-1]
            factors.extend(x.strip() for x in rhs.replace("*", " ").split() if x.strip().isdigit())
    if "has factors" in low or "trivially factors" in low:
        return {"status": "composite", "factors": factors}
    if "is prp" in low or "is 3-prp" in low or "fermat prp" in low:
        return {"status": "prp", "factors": factors}
    if "is prime" in low:
        return {"status": "prime", "factors": factors}
    return {"status": "unknown", "factors": factors, "tail": t[-1500:]}


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


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--pfgw", default="pfgw64", help="pfgw64 binary")
    ap.add_argument("--out", type=Path, default=Path("rank100-floors"))
    ap.add_argument("--start-k", type=int, default=K_DEAD + 2)
    ap.add_argument("--max-k", type=int, default=10_000)
    ap.add_argument("--timeout", type=int, default=0, help="seconds per k; 0 = no limit")
    ap.add_argument("--keep-going", action="store_true", help="do not stop on PRP")
    args = ap.parse_args()
    pfgw = Path(args.pfgw).expanduser()
    if not pfgw.is_absolute():
        pfgw = (Path.cwd() / pfgw).resolve()
    else:
        pfgw = pfgw.resolve()
    if not os.access(pfgw, os.X_OK):
        sys.exit(f"not executable: {pfgw}")
    args.out.mkdir(parents=True, exist_ok=True)
    logp = args.out / "floors.jsonl"
    done = load_done(logp)
    print(f"q = {A0}*2^{EXP}-1   start k>={args.start_k}  max {args.max_k}  pfgw {pfgw}", flush=True)
    if K_DEAD not in done:
        dead = {
            "k": K_DEAD,
            "eps": eps(K_DEAD),
            "expr": expr(K_DEAD),
            "status": "composite",
            "factors": ["162981019"],
            "seconds": 1234,
            "note": "pfgw 4.1.8 trial factor 2026-09-22",
        }
        logp.open("a").write(json.dumps(dead) + "\n")
        done[K_DEAD] = dead
    print(f"k={K_DEAD} composite, factor 162981019", flush=True)
    for k in admissible_from(args.start_k):
        if k > args.max_k:
            print("hit --max-k", args.max_k, flush=True)
            break
        e = expr(k)
        if k in done:
            print(f"skip k={k} {done[k].get('status')} {e}", flush=True)
            if done[k].get("status") in ("prp", "prime") and not args.keep_going:
                print("already have PRP; pass --keep-going to continue", flush=True)
                break
            continue
        print(f"\n=== k={k}  ε={eps(k):+}  {e} ===", flush=True)
        t0 = time.time()
        cmd = [str(pfgw), "-f", f"-q{e}"]
        try:
            proc = subprocess.run(
                cmd,
                cwd=str(pfgw.parent),
                capture_output=True,
                text=True,
                timeout=args.timeout or None,
            )
        except subprocess.TimeoutExpired as ex:
            row = {"k": k, "eps": eps(k), "expr": e, "status": "timeout", "seconds": time.time() - t0}
            logp.open("a").write(json.dumps(row) + "\n")
            print("timeout", flush=True)
            continue
        out = (proc.stdout or "") + (proc.stderr or "")
        (args.out / f"k{k}.log").write_text(out)
        parsed = parse_pfgw(out)
        row = {
            "k": k,
            "eps": eps(k),
            "expr": e,
            "status": parsed["status"],
            "factors": parsed.get("factors") or [],
            "returncode": proc.returncode,
            "seconds": round(time.time() - t0, 3),
        }
        if parsed["status"] == "unknown":
            row["tail"] = parsed.get("tail", "")[-500:]
        logp.open("a").write(json.dumps(row) + "\n")
        print(json.dumps({x: row[x] for x in row if x != "tail"}), flush=True)
        if row["status"] in ("prp", "prime") and not args.keep_going:
            print("PRP/prime — stopping. --keep-going to walk further.", flush=True)
            break
        if row["status"] == "unknown":
            print("unknown PFGW output — stopping.", flush=True)
            break


if __name__ == "__main__":
    main()
