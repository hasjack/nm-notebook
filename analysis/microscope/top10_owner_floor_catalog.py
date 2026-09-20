#!/usr/bin/env python3
"""Thin sieve: owner-floor certificates K_cert(q;B) for PrimePages top-ten primes.

Same method as mersenne_record_thin_sieve.py (validated: M_31 → K_cert=46).
Never materializes q. Works with q_mod_r via modular exponentiation.

Hire door facts (Doors.lean):
  m0(p) = p+1 if p%3==1 else p-1
  First-owner candidates: primes p = kq ± 1 with admissible k ≡ 2 or 4 (mod 6):
    k ≡ 2 (mod 6) → class A: p = kq - 1
    k ≡ 4 (mod 6) → class B: p = kq + 1

Forms:
  Mersenne  2^e - 1
  GFN       b^(2^n) + 1
  GU        b^(2^n) - b^(2^{n-1}) + 1

Class ↔ k depends on q mod 3 (critical for GFN with q≡2):
  q ≡ 1: k≡2 → A (p=kq-1), k≡4 → B (p=kq+1)
  q ≡ 2: k≡2 → B (p=kq+1), k≡4 → A (p=kq-1)  # flip; else r=3 kills all

Usage:
  python3 top10_owner_floor_catalog.py
  python3 top10_owner_floor_catalog.py --B 10000000 --validate-m31
  python3 top10_owner_floor_catalog.py --rank 1   # single rank (reuse known for #1)
"""
from __future__ import annotations

import argparse
import csv
import math
import os
import time
from dataclasses import dataclass, field
from typing import Callable, Dict, List, Optional, Tuple

# ---------------------------------------------------------------------------
# Top-ten catalog (PrimePages / t5k.org, late 2026)
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class DoorQ:
    rank: int
    label: str
    form: str  # "Mersenne" | "GFN" | "GU"
    digits: int
    # form-specific params
    e: Optional[int] = None          # Mersenne exponent
    b: Optional[int] = None          # GFN/GU base
    n: Optional[int] = None          # 2^n power (21 for 2097152)


TOP10: List[DoorQ] = [
    DoorQ(1, "2^136279841-1", "Mersenne", 41024320, e=136279841),
    DoorQ(2, "2^82589933-1", "Mersenne", 24862048, e=82589933),
    DoorQ(3, "2^77232917-1", "Mersenne", 23249425, e=77232917),
    DoorQ(4, "2^74207281-1", "Mersenne", 22338618, e=74207281),
    DoorQ(5, "2^57885161-1", "Mersenne", 17425170, e=57885161),
    DoorQ(6, "2524190^2097152+1", "GFN", 13426224, b=2524190, n=21),
    DoorQ(7, "2^43112609-1", "Mersenne", 12978189, e=43112609),
    DoorQ(8, "2^42643801-1", "Mersenne", 12837064, e=42643801),
    DoorQ(9, "516693^2097152-516693^1048576+1", "GU", 11981518, b=516693, n=21),
    DoorQ(10, "465859^2097152-465859^1048576+1", "GU", 11887192, b=465859, n=21),
]


def q_mod_r(door: DoorQ, r: int) -> int:
    """q mod r without materializing q."""
    if door.form == "Mersenne":
        assert door.e is not None
        return (pow(2, door.e, r) - 1) % r
    if door.form == "GFN":
        assert door.b is not None and door.n is not None
        return (pow(door.b, 1 << door.n, r) + 1) % r
    if door.form == "GU":
        assert door.b is not None and door.n is not None
        bn = pow(door.b, 1 << door.n, r)
        bh = pow(door.b, 1 << (door.n - 1), r)
        return (bn - bh + 1) % r
    raise ValueError(door.form)


def q_mod_3(door: DoorQ) -> int:
    return q_mod_r(door, 3)


def m0_desc(qmod3: int, door: DoorQ) -> str:
    """Describe m0(q) and whether it is a pure 2-power sink."""
    if qmod3 == 1:
        m0 = "q+1"
        sink = door.form == "Mersenne" and door.e is not None and door.e % 2 == 1
        # odd-e Mersenne: m0 = 2^e
        if sink:
            return f"m0=q+1=2^{door.e} (pure 2-power sink)"
        return f"m0=q+1 (not a 2-power sink)"
    if qmod3 == 2:
        return "m0=q-1 (not a 2-power sink)"
    return "q≡0 (mod 3) — unexpected for odd prime ≠3"


# ---------------------------------------------------------------------------
# Sieve primitives (from mersenne_record_thin_sieve.py)
# ---------------------------------------------------------------------------

def sieve_primes(limit: int) -> List[int]:
    if limit < 2:
        return []
    n = limit + 1
    is_p = bytearray(b"\x01") * n
    is_p[0] = is_p[1] = 0
    for i in range(2, int(math.isqrt(limit)) + 1):
        if is_p[i]:
            start = i * i
            is_p[start:n:i] = b"\x00" * (((n - 1 - start) // i) + 1)
    return [i for i in range(2, n) if is_p[i]]


def admissible_k_iter(start: int = 2):
    k = start if start >= 2 else 2
    while k % 6 not in (2, 4):
        k += 1
    while True:
        yield k
        if k % 6 == 2:
            k += 2
        else:
            k += 4


def build_forbidden(
    door: DoorQ, primes: List[int]
) -> Tuple[List[int], List[int], List[int], int]:
    rs: List[int] = []
    forb_A: List[int] = []
    forb_B: List[int] = []
    skipped = 0
    for r in primes:
        if r == 2:
            continue
        qmod = q_mod_r(door, r)
        if qmod == 0:
            skipped += 1
            continue
        inv = pow(qmod, -1, r)
        rs.append(r)
        forb_A.append(inv)            # k ≡ q^{-1}  ⇒ kq ≡ 1  ⇒ p=kq-1 ≡ 0
        forb_B.append((r - inv) % r)  # k ≡ -q^{-1} ⇒ kq ≡ -1 ⇒ p=kq+1 ≡ 0
    return rs, forb_A, forb_B, skipped


def class_of_k(k: int, qmod3: int) -> str:
    """Hire class for admissible k given q mod 3.

    q ≡ 1: k≡2 → A (p=kq-1), k≡4 → B (p=kq+1)   [Mersenne case]
    q ≡ 2: k≡2 → B (p=kq+1), k≡4 → A (p=kq-1)   [flip; else r=3 kills all]
    """
    if qmod3 == 1:
        return "A" if k % 6 == 2 else "B"
    if qmod3 == 2:
        return "B" if k % 6 == 2 else "A"
    raise ValueError(qmod3)


def first_survivor_with_kills(
    rs: List[int],
    forb_A: List[int],
    forb_B: List[int],
    k_cap: int,
    qmod3: int,
) -> Tuple[Optional[int], List[Tuple[int, str, int]]]:
    """Return (K_cert, kill_table) where kill_table is (k, class, first_r)."""
    kills: List[Tuple[int, str, int]] = []
    for k in admissible_k_iter(2):
        if k > k_cap:
            return None, kills
        cls = class_of_k(k, qmod3)
        hit = None
        # A uses forb_A (kq≡1), B uses forb_B (kq≡-1)
        if cls == "A":
            for r, fa in zip(rs, forb_A):
                if k % r == fa:
                    hit = r
                    break
        else:
            for r, fb in zip(rs, forb_B):
                if k % r == fb:
                    hit = r
                    break
        if hit is not None:
            kills.append((k, cls, hit))
            continue
        return k, kills
    return None, kills  # pragma: no cover


@dataclass
class CertResult:
    door: DoorQ
    B: int
    K_cert: Optional[int]
    kills: List[Tuple[int, str, int]]
    qmod3: int
    m0_note: str
    n_primes: int
    n_active_r: int
    skipped_qmod0: int
    wall_s: float
    sieve_s: float
    forb_s: float
    walk_s: float
    reused: bool = False


# Known #1 result (do not recompute unless --force-rank1)
KNOWN_RANK1 = CertResult(
    door=TOP10[0],
    B=10_000_000,
    K_cert=28,
    kills=[
        (2, "A", 375373),
        (4, "B", 5),
        (8, "A", 13),
        (10, "B", 11),
        (14, "A", 1181),
        (16, "B", 7),
        (20, "A", 79),
        (22, "B", 103),
        (26, "A", 5),
    ],
    qmod3=1,
    m0_note="m0=q+1=2^136279841 (pure 2-power sink)",
    n_primes=664579,
    n_active_r=0,  # not re-recorded; see mersenne_record note
    skipped_qmod0=0,
    wall_s=1.17,
    sieve_s=0.0,
    forb_s=0.0,
    walk_s=0.0,
    reused=True,
)


def certify(
    door: DoorQ,
    primes: List[int],
    B: int,
    k_cap: int,
    sieve_s: float,
) -> CertResult:
    t0 = time.perf_counter()
    qmod3 = q_mod_3(door)
    assert qmod3 in (1, 2), f"unexpected q mod 3 = {qmod3} for {door.label}"
    m0_note = m0_desc(qmod3, door)
    rs, forb_A, forb_B, skipped = build_forbidden(door, primes)
    t_forb = time.perf_counter()
    # escalate k_cap if needed
    cap = k_cap
    K: Optional[int] = None
    kills: List[Tuple[int, str, int]] = []
    while True:
        K, kills = first_survivor_with_kills(rs, forb_A, forb_B, cap, qmod3)
        if K is not None:
            break
        if cap >= 10_000_000:
            break
        cap = min(cap * 10, 10_000_000)
        print(f"  … escalating k_cap → {cap}", flush=True)
    t1 = time.perf_counter()
    return CertResult(
        door=door,
        B=B,
        K_cert=K,
        kills=kills,
        qmod3=qmod3,
        m0_note=m0_note,
        n_primes=len(primes),
        n_active_r=len(rs),
        skipped_qmod0=skipped,
        wall_s=t1 - t0 + sieve_s,  # include shared sieve amortized? report local+note
        sieve_s=sieve_s,
        forb_s=t_forb - t0,
        walk_s=t1 - t_forb,
        reused=False,
    )


def write_csv(path: str, results: List[CertResult]) -> None:
    with open(path, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow([
            "rank", "label", "form", "digits", "B", "K_cert", "n_kills",
            "q_mod_3", "m0_note", "wall_s", "forb_s", "walk_s",
            "n_active_r", "skipped_qmod0", "reused",
            "kill_table",  # k:class:r;...
        ])
        for r in results:
            kt = ";".join(f"{k}:{c}:{hit}" for k, c, hit in r.kills)
            w.writerow([
                r.door.rank, r.door.label, r.door.form, r.door.digits, r.B,
                r.K_cert, len(r.kills), r.qmod3, r.m0_note,
                f"{r.wall_s:.4f}", f"{r.forb_s:.4f}", f"{r.walk_s:.4f}",
                r.n_active_r, r.skipped_qmod0, int(r.reused), kt,
            ])


def write_md(path: str, results: List[CertResult], B: int) -> None:
    lines: List[str] = []
    lines.append("# Top-ten owner-floor certificates \(K_{\\mathrm{cert}}(q;B)\)")
    lines.append("")
    lines.append(f"- Source list: PrimePages / t5k.org top ten (late 2026).")
    lines.append(f"- Sieve bound: **\(B = {B:,}\)** (primary).")
    lines.append("- Papers frozen. Hunt closed. No paper edits. No \(N_{28}\) PRP.")
    lines.append("- Method identical to `mersenne_record_thin_sieve.py` (Mersenne record \(K_{\\mathrm{cert}}=28\)).")
    lines.append("- Never materializes \(q\); uses modular recipes for \(q \\bmod r\).")
    lines.append("")
    lines.append("## Hire door rules")
    lines.append("")
    lines.append("- \(m_0(p) = p+1\) if \(p\\equiv 1\\pmod{3}\), else \(p-1\) (`Hire/Doors.lean`).")
    lines.append("- First-owner candidates: primes \(p = kq\\pm 1\) with admissible \(k\\equiv 2\) or \(4\\pmod{6}\):")
    lines.append("  - \(k\\equiv 2\\pmod{6}\) → class A: \(p = kq - 1\)")
    lines.append("  - \(k\\equiv 4\\pmod{6}\) → class B: \(p = kq + 1\)")
    lines.append("- For each odd prime \(r\\le B\): eliminate admissible \(k\) with candidate \(\\equiv 0\\pmod{r}\).")
    lines.append("- \(K_{\\mathrm{cert}}\) = first admissible \(k\) that survives all \(r\\le B\).")
    lines.append("- Sanity: \(M_{31}\) → \(K_{\\mathrm{cert}}=46\) (known first owner).")
    lines.append("")
    lines.append("## Modular \(q \\bmod r\) recipes")
    lines.append("")
    lines.append("| form | recipe |")
    lines.append("|---|---|")
    lines.append("| Mersenne \(2^e-1\) | `(pow(2,e,r)-1) % r` |")
    lines.append("| GFN \(b^{2^n}+1\) | `(pow(b,1<<n,r)+1) % r` |")
    lines.append("| GU \(b^{2^n}-b^{2^{n-1}}+1\) | `(pow(b,1<<n,r)-pow(b,1<<(n-1),r)+1) % r` |")
    lines.append("")
    lines.append("## Summary table")
    lines.append("")
    lines.append("| rank | form | digits | \(q\\bmod 3\) | \(K_{\\mathrm{cert}}(q;10^7)\) | #kills | wall | m0 note |")
    lines.append("|---:|---|---:|---:|---:|---:|---:|---|")
    for r in results:
        wall = f"{r.wall_s:.2f}s" + (" (reused)" if r.reused else "")
        lines.append(
            f"| {r.door.rank} | `{r.door.label}` ({r.door.form}) | "
            f"{r.door.digits:,} | {r.qmod3} | **{r.K_cert}** | {len(r.kills)} | "
            f"{wall} | {r.m0_note} |"
        )
    lines.append("")
    lines.append("## Door / sink ping (non-Mersenne)")
    lines.append("")
    lines.append("Sink (\(m_0\) pure \(2\)-power) occurs **only** for odd-exponent Mersennes "
                 "(\(m_0(q)=q+1=2^e\)). Non-Mersenne doors:")
    lines.append("")
    for r in results:
        if r.door.form == "Mersenne":
            continue
        lines.append(f"- rank {r.door.rank} `{r.door.label}`: \(q\\equiv {r.qmod3}\\pmod{{3}}\) → {r.m0_note}.")
    lines.append("")
    lines.append("## Kill tables (admissible \(k < K_{\\mathrm{cert}}\), first factor \(r\\le B\))")
    lines.append("")
    for r in results:
        lines.append(f"### rank {r.door.rank}: `{r.door.label}` — "
                     f"\(K_{{\\mathrm{{cert}}}}={r.K_cert}\), {len(r.kills)} kills")
        lines.append("")
        if not r.kills:
            lines.append("(no kills below \(K_{\\mathrm{cert}}\) — elementary floor already tight, or \(K=2\) survivor)")
            lines.append("")
            continue
        lines.append("| \(k\) | class | first \(r\\le B\) |")
        lines.append("|---:|:---:|---:|")
        for k, c, hit in r.kills:
            lines.append(f"| {k} | {c} | {hit} |")
        cls = class_of_k(r.K_cert, r.qmod3) if r.K_cert else "?"
        lines.append(f"| **{r.K_cert}** | **{cls}** | **survives** |")
        lines.append("")
    lines.append("## Caveats")
    lines.append("")
    lines.append("1. \(K_{\\mathrm{cert}}\) is a **lower** bound on the first-owner multiplier. "
                 "Survivors may still be composite (large factors).")
    lines.append("2. Equality \(kq\\pm 1 = r\) is impossible for \(k\\ge 2\) and \(r\\le B\\ll q\); no false kills.")
    lines.append("3. No search for \(\\tau(q)\); no primality tests on multi-million-digit candidates.")
    lines.append("4. Rank 1 reused from the frozen Mersenne-record catalog (\(K_{\\mathrm{cert}}=28\) at \(B=10^7\)).")
    lines.append("")
    lines.append("## Artifacts")
    lines.append("")
    lines.append("- `drafts/top10_owner_floor_catalog.py` — this script")
    lines.append("- `drafts/top10_owner_floor_catalog.md` — this note")
    lines.append("- `drafts/top10_owner_floor_catalog.csv` — machine-readable rows + kill tables")
    lines.append("- Sync copies under `analysis/microscope/`")
    lines.append("")
    lines.append("## Paste-ready room takeaway")
    lines.append("")
    # build compact table for takeaway
    rows = " | ".join(
        f"{r.door.rank}:{r.K_cert}" for r in results
    )
    lines.append(
        f"**Top-10 thin-sieve owner floors at \(B=10^7\):** "
        + ", ".join(f"#{r.door.rank} \(K={r.K_cert}\)" for r in results)
        + f". Rank #1 is the known Mersenne-record **28**. "
        f"Non-Mersenne doors are not 2-power sinks "
        f"(GFN #6: \(q\\equiv 2\\pmod{{3}}\); GU #9,#10: \(q\\equiv 1\\pmod{{3}}\)). "
        f"Kill receipts for every admissible \(k<K_{{\\mathrm{{cert}}}}\). Papers frozen; hunt closed."
    )
    lines.append("")
    with open(path, "w") as f:
        f.write("\n".join(lines) + "\n")


def validate_m31(primes: List[int]) -> None:
    door = DoorQ(0, "2^31-1", "Mersenne", 10, e=31)
    # use primes ≤ 1e5 for the classic validation
    primes_1e5 = [p for p in primes if p <= 100_000]
    if not primes_1e5 or primes_1e5[-1] < 100_000:
        primes_1e5 = sieve_primes(100_000)
    rs, forb_A, forb_B, _ = build_forbidden(door, primes_1e5)
    K, kills = first_survivor_with_kills(rs, forb_A, forb_B, 1000, 1)
    assert K == 46, (K, kills)
    print(f"M31 validation OK: K_cert=46 ({len(kills)} kills)", flush=True)


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--B", type=int, default=10_000_000, help="sieve prime bound")
    ap.add_argument("--k-cap", type=int, default=100_000,
                    help="initial max admissible k (auto-escalates)")
    ap.add_argument("--rank", type=int, default=0,
                    help="if 1..10, only that rank; 0 = all")
    ap.add_argument("--force-rank1", action="store_true",
                    help="recompute rank 1 instead of reusing K_cert=28")
    ap.add_argument("--validate-m31", action="store_true")
    ap.add_argument("--confirm-B", type=int, default=0,
                    help="optional second bound (e.g. 1e8) for a couple ranks")
    ap.add_argument("--out-dir", type=str,
                    default="/workspace/e-walk-lean/drafts")
    args = ap.parse_args()

    t_sieve0 = time.perf_counter()
    print(f"sieving primes ≤ {args.B} …", flush=True)
    primes = sieve_primes(args.B)
    sieve_s = time.perf_counter() - t_sieve0
    print(f"  {len(primes)} primes in {sieve_s:.3f}s", flush=True)

    if args.validate_m31:
        validate_m31(primes)

    doors = TOP10
    if args.rank:
        doors = [d for d in TOP10 if d.rank == args.rank]
        assert doors, f"bad rank {args.rank}"

    results: List[CertResult] = []
    for door in doors:
        print(f"\n=== rank {door.rank}: {door.label} ({door.form}) ===", flush=True)
        if door.rank == 1 and args.B == 10_000_000 and not args.force_rank1:
            # reuse known catalog; still compute qmod3 for the summary
            r = CertResult(
                door=door,
                B=args.B,
                K_cert=KNOWN_RANK1.K_cert,
                kills=list(KNOWN_RANK1.kills),
                qmod3=q_mod_3(door),
                m0_note=m0_desc(q_mod_3(door), door),
                n_primes=len(primes),
                n_active_r=KNOWN_RANK1.n_active_r,
                skipped_qmod0=KNOWN_RANK1.skipped_qmod0,
                wall_s=KNOWN_RANK1.wall_s,
                sieve_s=sieve_s,
                forb_s=0.0,
                walk_s=0.0,
                reused=True,
            )
            print(f"  REUSED K_cert={r.K_cert}  kills={len(r.kills)}  "
                  f"qmod3={r.qmod3}  {r.m0_note}", flush=True)
        else:
            r = certify(door, primes, args.B, args.k_cap, sieve_s=0.0)
            # wall_s in certify excludes shared sieve; report local forb+walk
            r.wall_s = r.forb_s + r.walk_s
            print(
                f"  K_cert={r.K_cert}  kills={len(r.kills)}  qmod3={r.qmod3}  "
                f"active_r={r.n_active_r}/{r.n_primes}  skip0={r.skipped_qmod0}",
                flush=True,
            )
            print(
                f"  wall={r.wall_s:.3f}s  (forb {r.forb_s:.3f}s, walk {r.walk_s:.3f}s)  "
                f"{r.m0_note}",
                flush=True,
            )
            if r.kills:
                preview = ", ".join(f"{k}:{c}:{hit}" for k, c, hit in r.kills[:8])
                more = "" if len(r.kills) <= 8 else f" … +{len(r.kills)-8}"
                print(f"  kills: {preview}{more}", flush=True)
        results.append(r)

        # optional confirm at larger B for a couple
        if args.confirm_B and args.confirm_B > args.B and door.rank in (2, 6, 9):
            print(f"  confirming at B={args.confirm_B} …", flush=True)
            primes2 = sieve_primes(args.confirm_B)
            r2 = certify(door, primes2, args.confirm_B, args.k_cap, sieve_s=0.0)
            r2.wall_s = r2.forb_s + r2.walk_s
            same = "SAME" if r2.K_cert == r.K_cert else f"CHANGED {r.K_cert}→{r2.K_cert}"
            print(f"  confirm K_cert={r2.K_cert} ({same}) wall={r2.wall_s:.3f}s", flush=True)

    os.makedirs(args.out_dir, exist_ok=True)
    csv_path = os.path.join(args.out_dir, "top10_owner_floor_catalog.csv")
    md_path = os.path.join(args.out_dir, "top10_owner_floor_catalog.md")
    write_csv(csv_path, results)
    write_md(md_path, results, args.B)
    print(f"\nWrote {csv_path}", flush=True)
    print(f"Wrote {md_path}", flush=True)

    # paste-ready one-liner
    print("\n--- PASTE-READY ---", flush=True)
    cells = " | ".join(
        f"{r.door.rank} | {r.door.form[:3]} | {r.door.digits} | {r.K_cert} | {len(r.kills)} | {r.wall_s:.2f}s"
        for r in results
    )
    print(
        "rank|form|digits|K_cert(1e7)|#kills|wall → "
        + " || ".join(
            f"#{r.door.rank} {r.door.form} {r.door.digits} K={r.K_cert} kills={len(r.kills)} {r.wall_s:.2f}s"
            for r in results
        ),
        flush=True,
    )
    print(
        f"Top-10 K_cert(q;1e7): "
        + ", ".join(f"#{r.door.rank}={r.K_cert}" for r in results)
        + " (#1 reused=28).",
        flush=True,
    )


if __name__ == "__main__":
    main()
