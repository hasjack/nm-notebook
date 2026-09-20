#!/usr/bin/env python3
"""Thin sieve: owner-floor certificates K_cert(q;B) for PrimePages top-100 primes.

Extends top10_owner_floor_catalog.py to ranks 1..100 at fixed B=10^7.
Hunt freakishly high K_cert and compression ratio (digits / #kills), NOT rank chasing.
Papers frozen. Hunt closed. No full PRP lottery.

Method (identical to top-10 / mersenne_record_thin_sieve):
  Never materialize q. Admissible k ≡ 2 or 4 (mod 6); kill kq±1 by r≤B.
  Class flip when q≡2 (mod 3).

Compression definition (documented):
  compression_ratio = digits(q) / max(1, n_kills)
  i.e. decimal digits of q per kill-receipt (witness triple). When n_kills=0
  (K_cert=2 floor-tight), ratio = digits (treated as "infinite"/floor-tight).

Usage:
  python3 top100_owner_floor_catalog.py
  python3 top100_owner_floor_catalog.py --B 10000000 --validate-m31
  python3 top100_owner_floor_catalog.py --list-only   # parse+classify, no sieve
"""
from __future__ import annotations

import argparse
import csv
import math
import os
import re
import shutil
import time
from dataclasses import dataclass
from typing import List, Optional, Tuple

# ---------------------------------------------------------------------------
# Door form
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class DoorQ:
    rank: int
    label: str
    form: str  # Mersenne|GFN|GU|Proth|Riesel|GenPow|GaussMersenne|Skip
    digits: int
    # form-specific params (optional)
    e: Optional[int] = None          # Mersenne / Gauss exponent pieces
    b: Optional[int] = None
    n: Optional[int] = None          # for GFN/GU: log2 of power; else exponent
    k: Optional[int] = None          # Proth/Riesel/GenPow multiplier
    sign: Optional[int] = None       # +1 or -1 for k*b^n ± 1
    skip_reason: Optional[str] = None


def is_power_of_two(x: int) -> bool:
    return x > 0 and (x & (x - 1)) == 0


def log2_exact(x: int) -> Optional[int]:
    if not is_power_of_two(x):
        return None
    return x.bit_length() - 1


def parse_expression(rank: int, expr: str, digits: int) -> DoorQ:
    """Parse a PrimePages expression into a DoorQ with modular recipe, or Skip."""
    s = expr.replace(" ", "")

    # Primorial / factorial / compositorials — cannot modularize cheaply
    if "#" in s or "!" in s:
        return DoorQ(rank, expr, "Skip", digits, skip_reason="primorial/factorial/compositorial")

    # Mersenne 2^e-1
    m = re.fullmatch(r"2\^(\d+)-1", s)
    if m:
        return DoorQ(rank, expr, "Mersenne", digits, e=int(m.group(1)))

    # GU / Phi_3(b^h): b^{2h} - b^h + 1  (n = log2(2h) when power-of-two; else store h in e)
    m = re.fullmatch(r"(\d+)\^(\d+)-\1\^(\d+)\+1", s)
    if m:
        b, p, h = int(m.group(1)), int(m.group(2)), int(m.group(3))
        if p == 2 * h:
            if is_power_of_two(p):
                n = log2_exact(p)
                assert n is not None
                return DoorQ(rank, expr, "GU", digits, b=b, n=n)
            # Generalized unique with non-2-power height (e.g. h=393216=3*2^17)
            return DoorQ(rank, expr, "GU", digits, b=b, e=h)  # e = half-exponent

    # Gaussian Mersenne / related: 2^a ± 2^b + 1
    m = re.fullmatch(r"2\^(\d+)\+2\^(\d+)\+1", s)
    if m:
        e2, e1 = int(m.group(1)), int(m.group(2))
        # standard GM: a=2b; or odd-p form a=2b-1 (e.g. #67)
        if e2 == 2 * e1 or e2 == 2 * e1 - 1:
            return DoorQ(rank, expr, "GaussMersenne", digits, e=e1, n=e2, sign=1)
    m = re.fullmatch(r"2\^(\d+)-2\^(\d+)\+1", s)
    if m:
        e2, e1 = int(m.group(1)), int(m.group(2))
        if e2 == 2 * e1 or e2 == 2 * e1 - 1:
            return DoorQ(rank, expr, "GaussMersenne", digits, e=e1, n=e2, sign=-1)

    # GFN: b^(2^n)+1  (pure power-of-two exponent, no k multiplier)
    m = re.fullmatch(r"(\d+)\^(\d+)\+1", s)
    if m:
        b, p = int(m.group(1)), int(m.group(2))
        if is_power_of_two(p) and p >= 2:
            n = log2_exact(p)
            assert n is not None
            return DoorQ(rank, expr, "GFN", digits, b=b, n=n)

    # (10^a+1)^2-2 = 10^{2a} + 2*10^a - 1
    m = re.fullmatch(r"\(10\^(\d+)\+1\)\^2-2", s)
    if m:
        a = int(m.group(1))
        return DoorQ(rank, expr, "GenPow", digits, k=1, b=10, n=2 * a, sign=1,
                     e=a)  # e stores half-exponent for special recipe

    # k*b^n ± 1  (covers Proth/Riesel k*2^n±1, Cullen n*b^n±1, near-repdigit, etc.)
    m = re.fullmatch(r"(\d+)\*(\d+)\^(\d+)([+-])1", s)
    if m:
        kk, bb, nn, sg = int(m.group(1)), int(m.group(2)), int(m.group(3)), m.group(4)
        sign = 1 if sg == "+" else -1
        if bb == 2:
            form = "Proth" if sign == 1 else "Riesel"
        else:
            form = "GenPow"
        return DoorQ(rank, expr, form, digits, k=kk, b=bb, n=nn, sign=sign)

    return DoorQ(rank, expr, "Skip", digits, skip_reason=f"unparsed exotic: {expr}")


def load_top100(path: str) -> List[DoorQ]:
    """Parse t5k all.txt (or any similar table) for ranks 1..100."""
    text = open(path).read().splitlines()
    started = False
    doors: List[DoorQ] = []
    seen = set()
    for line in text:
        if re.match(r"^-----", line):
            started = True
            continue
        if not started:
            continue
        m = re.match(
            r"^\s*(\d+)[a-z]?\s+(\S.*?)\s+(\d+)\s+\S+\s+\d{4}",
            line,
        )
        if not m:
            continue
        rank = int(m.group(1))
        if rank > 100:
            break
        if rank in seen:
            continue
        seen.add(rank)
        expr = m.group(2).strip()
        digits = int(m.group(3))
        doors.append(parse_expression(rank, expr, digits))
    doors.sort(key=lambda d: d.rank)
    return doors


def q_mod_r(door: DoorQ, r: int) -> int:
    """q mod r without materializing q."""
    if door.form == "Mersenne":
        assert door.e is not None
        return (pow(2, door.e, r) - 1) % r
    if door.form == "GFN":
        assert door.b is not None and door.n is not None
        return (pow(door.b, 1 << door.n, r) + 1) % r
    if door.form == "GU":
        assert door.b is not None
        if door.n is not None:
            bn = pow(door.b, 1 << door.n, r)
            bh = pow(door.b, 1 << (door.n - 1), r)
        else:
            # e stores half-exponent h; q = b^{2h} - b^h + 1
            assert door.e is not None
            bh = pow(door.b, door.e, r)
            bn = pow(door.b, 2 * door.e, r)
        return (bn - bh + 1) % r
    if door.form == "GaussMersenne":
        assert door.e is not None and door.sign is not None
        # 2^n ± 2^e + 1  (n stored; default 2e if absent)
        e2 = door.n if door.n is not None else 2 * door.e
        return (pow(2, e2, r) + door.sign * pow(2, door.e, r) + 1) % r
    if door.form in ("Proth", "Riesel", "GenPow"):
        assert door.k is not None and door.b is not None and door.n is not None
        assert door.sign is not None
        # Special: (10^a+1)^2-2 stored as GenPow with e=a half
        if door.e is not None and door.b == 10 and door.label.startswith("(10^"):
            a = door.e
            ta = pow(10, a, r)
            return (ta * ta + 2 * ta - 1) % r
        return (door.k * pow(door.b, door.n, r) + door.sign) % r
    raise ValueError(f"no modular recipe for {door.form}: {door.label}")


def q_mod_3(door: DoorQ) -> int:
    return q_mod_r(door, 3)


def m0_desc(qmod3: int, door: DoorQ) -> str:
    if qmod3 == 1:
        if door.form == "Mersenne" and door.e is not None and door.e % 2 == 1:
            return f"m0=q+1=2^{door.e} (pure 2-power sink)"
        return "m0=q+1 (not a 2-power sink)"
    if qmod3 == 2:
        return "m0=q-1 (not a 2-power sink)"
    return "q≡0 (mod 3) — unexpected for odd prime ≠3"


# ---------------------------------------------------------------------------
# Sieve primitives
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
        forb_A.append(inv)
        forb_B.append((r - inv) % r)
    return rs, forb_A, forb_B, skipped


def class_of_k(k: int, qmod3: int) -> str:
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
    kills: List[Tuple[int, str, int]] = []
    for k in admissible_k_iter(2):
        if k > k_cap:
            return None, kills
        cls = class_of_k(k, qmod3)
        hit = None
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


def compression_ratio(digits: int, n_kills: int) -> float:
    """digits(q) / max(1, n_kills) — digits certified per kill receipt."""
    return digits / max(1, n_kills)


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
    forb_s: float
    walk_s: float
    reused: bool = False
    skipped: bool = False
    skip_reason: str = ""

    @property
    def n_kills(self) -> int:
        return len(self.kills)

    @property
    def compression(self) -> float:
        if self.skipped or self.K_cert is None:
            return 0.0
        return compression_ratio(self.door.digits, self.n_kills)

    @property
    def survivor_label(self) -> str:
        if self.skipped or self.K_cert is None:
            return ""
        cls = class_of_k(self.K_cert, self.qmod3)
        # ε: A → −1 (kq−1), B → +1 (kq+1)
        eps = "-1" if cls == "A" else "+1"
        return f"k={self.K_cert}, ε={eps} (class {cls})"


# Known #1 result
KNOWN_RANK1_KILLS = [
    (2, "A", 375373), (4, "B", 5), (8, "A", 13), (10, "B", 11),
    (14, "A", 1181), (16, "B", 7), (20, "A", 79), (22, "B", 103), (26, "A", 5),
]


def certify(
    door: DoorQ,
    primes: List[int],
    B: int,
    k_cap: int,
) -> CertResult:
    t0 = time.perf_counter()
    qmod3 = q_mod_3(door)
    assert qmod3 in (1, 2), f"unexpected q mod 3 = {qmod3} for {door.label}"
    m0_note = m0_desc(qmod3, door)
    rs, forb_A, forb_B, skipped = build_forbidden(door, primes)
    t_forb = time.perf_counter()
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
        wall_s=t1 - t0,
        forb_s=t_forb - t0,
        walk_s=t1 - t_forb,
        reused=False,
    )


def write_csv(path: str, results: List[CertResult]) -> None:
    with open(path, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow([
            "rank", "label", "form", "digits", "B", "K_cert", "n_kills",
            "compression_ratio", "q_mod_3", "m0_note", "wall_s", "forb_s", "walk_s",
            "n_active_r", "skipped_qmod0", "reused", "skipped", "skip_reason",
            "first_survivor", "kill_table",
        ])
        for r in results:
            kt = ";".join(f"{k}:{c}:{hit}" for k, c, hit in r.kills)
            w.writerow([
                r.door.rank, r.door.label, r.door.form, r.door.digits, r.B,
                r.K_cert if not r.skipped else "",
                r.n_kills if not r.skipped else "",
                f"{r.compression:.6g}" if not r.skipped else "",
                r.qmod3 if not r.skipped else "",
                r.m0_note if not r.skipped else "",
                f"{r.wall_s:.4f}", f"{r.forb_s:.4f}", f"{r.walk_s:.4f}",
                r.n_active_r, r.skipped_qmod0, int(r.reused),
                int(r.skipped), r.skip_reason,
                r.survivor_label, kt,
            ])


def write_md(
    path: str,
    results: List[CertResult],
    B: int,
    source_note: str,
    timing_note: str,
) -> None:
    processed = [r for r in results if not r.skipped]
    skipped = [r for r in results if r.skipped]
    lines: List[str] = []
    lines.append("# Top-100 owner-floor certificates \(K_{\\mathrm{cert}}(q;B)\)")
    lines.append("")
    lines.append(f"- Source: {source_note}")
    lines.append(f"- Sieve bound: **\(B = {B:,}\)** (fixed).")
    lines.append("- Papers frozen. Hunt closed. No paper edits. No full PRP lottery.")
    lines.append("- Method identical to `top10_owner_floor_catalog.py` / `mersenne_record_thin_sieve.py`.")
    lines.append("- Never materializes \(q\); modular recipes for \(q \\bmod r\).")
    lines.append(f"- Processed: **{len(processed)}** / Skipped: **{len(skipped)}** of {len(results)}.")
    lines.append("")
    lines.append("## Compression definition")
    lines.append("")
    lines.append(
        "**compression_ratio** = `digits(q) / max(1, n_kills)` — decimal digits of \(q\) "
        "per kill-receipt (witness triple \\((k,\\mathrm{class},r)\\)). "
        "When `n_kills=0` (\(K_{\\mathrm{cert}}=2\), floor-tight), ratio equals `digits` "
        "(treated as floor-tight / formally infinite). "
        "This is the hunt metric alongside raw \(K_{\\mathrm{cert}}\); **not** rank chasing."
    )
    lines.append("")
    lines.append("## Hire door rules")
    lines.append("")
    lines.append("- \(m_0(p) = p+1\) if \(p\\equiv 1\\pmod{3}\), else \(p-1\`.")
    lines.append("- Admissible \(k\\equiv 2\) or \(4\\pmod{6}\); class A: \(p=kq-1\), class B: \(p=kq+1\).")
    lines.append("- Class ↔ \(k\) **flips** when \(q\\equiv 2\\pmod{3}\) (else \(r=3\) kills all).")
    lines.append("- \(K_{\\mathrm{cert}}\) = first admissible \(k\) surviving all \(r\\le B\).")
    lines.append("")
    lines.append("## Modular recipes")
    lines.append("")
    lines.append("| form | recipe |")
    lines.append("|---|---|")
    lines.append("| Mersenne \(2^e-1\) | `(pow(2,e,r)-1)%r` |")
    lines.append("| GFN \(b^{2^n}+1\) | `(pow(b,1<<n,r)+1)%r` |")
    lines.append("| GU \(b^{2^n}-b^{2^{n-1}}+1\) | `(bn-bh+1)%r` |")
    lines.append("| Proth/Riesel \(k\\cdot 2^n\\pm 1\) | `(k*pow(2,n,r)±1)%r` |")
    lines.append("| GenPow \(k\\cdot b^n\\pm 1\) | `(k*pow(b,n,r)±1)%r` |")
    lines.append("| GaussMersenne \(2^{2e}\\pm 2^e+1\) | `(t*t±t+1)%r` |")
    lines.append("| \((10^a+1)^2-2\) | `(ta^2+2*ta-1)%r` |")
    lines.append("")

    # Leaderboards
    by_K = sorted(processed, key=lambda r: (-(r.K_cert or 0), r.door.rank))
    by_C = sorted(processed, key=lambda r: (-r.compression, r.door.rank))

    lines.append("## Leaderboard: top 10 by \(K_{\\mathrm{cert}}\)")
    lines.append("")
    lines.append("| # | rank | form | digits | \(K_{\\mathrm{cert}}\) | #kills | compression | first survivor |")
    lines.append("|---:|---:|---|---:|---:|---:|---:|---|")
    for i, r in enumerate(by_K[:10], 1):
        lines.append(
            f"| {i} | {r.door.rank} | `{r.door.label}` ({r.door.form}) | "
            f"{r.door.digits:,} | **{r.K_cert}** | {r.n_kills} | "
            f"{r.compression:,.3g} | {r.survivor_label} |"
        )
    lines.append("")
    lines.append("## Leaderboard: top 10 by compression ratio")
    lines.append("")
    lines.append("| # | rank | form | digits | \(K_{\\mathrm{cert}}\) | #kills | compression | note |")
    lines.append("|---:|---:|---|---:|---:|---:|---:|---|")
    for i, r in enumerate(by_C[:10], 1):
        note = "floor-tight" if r.n_kills == 0 else ""
        lines.append(
            f"| {i} | {r.door.rank} | `{r.door.label}` ({r.door.form}) | "
            f"{r.door.digits:,} | {r.K_cert} | {r.n_kills} | "
            f"**{r.compression:,.3g}** | {note} |"
        )
    lines.append("")

    # Freak highlight: high K among non-tiny
    freaks = [r for r in by_K if (r.K_cert or 0) >= 50]
    lines.append("## Freak floors (\(K_{\\mathrm{cert}}\\ge 50\))")
    lines.append("")
    if not freaks:
        lines.append("(none at this threshold)")
    else:
        lines.append("| rank | form | digits | \(K\) | #kills | compression | wall |")
        lines.append("|---:|---|---:|---:|---:|---:|---:|")
        for r in freaks:
            lines.append(
                f"| {r.door.rank} | `{r.door.label}` ({r.door.form}) | "
                f"{r.door.digits:,} | **{r.K_cert}** | {r.n_kills} | "
                f"{r.compression:,.3g} | {r.wall_s:.2f}s |"
            )
    lines.append("")

    lines.append("## Full summary table")
    lines.append("")
    lines.append(
        "| rank | form | digits | \(q\\bmod 3\) | \(K_{\\mathrm{cert}}\) | #kills | "
        "compression | wall | first survivor |"
    )
    lines.append("|---:|---|---:|---:|---:|---:|---:|---:|---|")
    for r in results:
        if r.skipped:
            lines.append(
                f"| {r.door.rank} | `{r.door.label}` (**SKIP**) | "
                f"{r.door.digits:,} | — | — | — | — | — | {r.skip_reason} |"
            )
            continue
        wall = f"{r.wall_s:.2f}s" + (" (reused)" if r.reused else "")
        lines.append(
            f"| {r.door.rank} | `{r.door.label}` ({r.door.form}) | "
            f"{r.door.digits:,} | {r.qmod3} | **{r.K_cert}** | {r.n_kills} | "
            f"{r.compression:,.3g} | {wall} | {r.survivor_label} |"
        )
    lines.append("")

    if skipped:
        lines.append("## Skip list")
        lines.append("")
        for r in skipped:
            lines.append(f"- rank {r.door.rank} `{r.door.label}`: {r.skip_reason}")
        lines.append("")

    lines.append("## Timing note: top-10 #10 first survivor (GU, \(K=92\))")
    lines.append("")
    lines.append(timing_note)
    lines.append("")

    lines.append("## Caveats")
    lines.append("")
    lines.append(
        "1. \(K_{\\mathrm{cert}}\) is a **lower** bound on the first-owner multiplier; "
        "survivors may still be composite."
    )
    lines.append("2. Equality \(kq\\pm 1 = r\) is impossible for \(k\\ge 2\) and \(r\\le B\\ll q\).")
    lines.append("3. No \(\\tau(q)\) search; no multi-million-digit PRP lottery.")
    lines.append("4. Rank 1 reused from frozen Mersenne-record catalog when \(B=10^7\).")
    lines.append("")

    lines.append("## Artifacts")
    lines.append("")
    lines.append("- `drafts/top100_owner_floor_catalog.py`")
    lines.append("- `drafts/top100_owner_floor_catalog.md`")
    lines.append("- `drafts/top100_owner_floor_catalog.csv`")
    lines.append("- Sync copies under `analysis/microscope/`")
    lines.append("")

    # Paste-ready takeaway
    topK = by_K[:5]
    topC_nonzero = [r for r in by_C if r.n_kills > 0][:5]
    freak_str = ", ".join(
        f"#{r.door.rank} \(K={r.K_cert}\)" for r in freaks[:8]
    ) or "(none ≥50)"
    lines.append("## Paste-ready room takeaway")
    lines.append("")
    takeaway = (
        f"**Top-100 thin-sieve owner floors at \(B=10^7\):** "
        f"processed {len(processed)}/{len(results)} modular forms "
        f"(skipped {len(skipped)}: "
        + (", ".join(f"#{r.door.rank}" for r in skipped) or "none")
        + "). "
        f"**Freak \(K_{{\\mathrm{{cert}}}}\\ge 50\):** {freak_str}. "
        f"Top-\(K\) leaders: "
        + ", ".join(f"#{r.door.rank}={r.K_cert}" for r in topK)
        + ". "
        f"Compression = digits/#kills; top non-floor-tight: "
        + ", ".join(
            f"#{r.door.rank}={r.compression:.3g}" for r in topC_nonzero
        )
        + ". "
        f"Class flip for \(q\\equiv 2\\pmod{{3}}\) retained. "
        f"Papers frozen; hunt closed; no PRP lottery."
    )
    lines.append(takeaway)
    lines.append("")

    with open(path, "w") as f:
        f.write("\n".join(lines) + "\n")
    return takeaway


def validate_m31(primes: List[int]) -> None:
    door = DoorQ(0, "2^31-1", "Mersenne", 10, e=31)
    primes_1e5 = [p for p in primes if p <= 100_000] or sieve_primes(100_000)
    rs, forb_A, forb_B, _ = build_forbidden(door, primes_1e5)
    K, kills = first_survivor_with_kills(rs, forb_A, forb_B, 1000, 1)
    assert K == 46, (K, kills)
    print(f"M31 validation OK: K_cert=46 ({len(kills)} kills)", flush=True)


def timing_note_rank10() -> str:
    """One-line feasibility note for a modular Fermat/PRP probe on #10 survivor."""
    # GU 465859^2097152-… has ~11.9M digits. One Fermat iteration a^(N-1) mod N
    # needs FFT mul on ~40 Mbit operands. Without gwnum/PFGW/llr on this box,
    # a cheap modular probe is not feasible.
    return (
        "Top-10 #10 first survivor (GU `465859^2097152-465859^1048576+1`, \(K=92\), "
        "~11.9M digits): one modular Fermat/PRP iteration needs specialised FFT "
        "arithmetic (gwnum / PFGW / LLR) on ~40-Mbit operands — **not feasible "
        "cheaply on this box without those tools**; no short probe started, no full PRP."
    )


def main() -> None:
    ap = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    ap.add_argument("--B", type=int, default=10_000_000)
    ap.add_argument("--k-cap", type=int, default=100_000)
    ap.add_argument("--rank", type=int, default=0, help="single rank, 0=all")
    ap.add_argument("--force-rank1", action="store_true")
    ap.add_argument("--validate-m31", action="store_true")
    ap.add_argument("--list-only", action="store_true")
    ap.add_argument(
        "--t5k",
        type=str,
        default="/workspace/e-walk-lean/drafts/t5k_all.txt",
    )
    ap.add_argument(
        "--out-dir",
        type=str,
        default="/workspace/e-walk-lean/drafts",
    )
    ap.add_argument(
        "--copy-dir",
        type=str,
        default="/workspace/analysis/microscope",
    )
    args = ap.parse_args()

    doors = load_top100(args.t5k)
    assert len(doors) == 100, f"expected 100 doors, got {len(doors)}"
    print(f"Loaded {len(doors)} doors from {args.t5k}", flush=True)

    form_counts: dict = {}
    for d in doors:
        form_counts[d.form] = form_counts.get(d.form, 0) + 1
    print("Form counts:", form_counts, flush=True)
    for d in doors:
        if d.form == "Skip":
            print(f"  SKIP #{d.rank} {d.label}: {d.skip_reason}", flush=True)

    if args.list_only:
        return

    if args.rank:
        doors = [d for d in doors if d.rank == args.rank]
        assert doors, f"bad rank {args.rank}"

    t_sieve0 = time.perf_counter()
    print(f"sieving primes ≤ {args.B} …", flush=True)
    primes = sieve_primes(args.B)
    sieve_s = time.perf_counter() - t_sieve0
    print(f"  {len(primes)} primes in {sieve_s:.3f}s", flush=True)

    if args.validate_m31:
        validate_m31(primes)

    results: List[CertResult] = []
    for door in doors:
        print(
            f"\n=== rank {door.rank}: {door.label} ({door.form}) "
            f"digits={door.digits} ===",
            flush=True,
        )
        if door.form == "Skip":
            r = CertResult(
                door=door, B=args.B, K_cert=None, kills=[], qmod3=0,
                m0_note="", n_primes=len(primes), n_active_r=0,
                skipped_qmod0=0, wall_s=0.0, forb_s=0.0, walk_s=0.0,
                skipped=True, skip_reason=door.skip_reason or "skip",
            )
            print(f"  SKIPPED: {r.skip_reason}", flush=True)
            results.append(r)
            continue

        if (
            door.rank == 1
            and args.B == 10_000_000
            and not args.force_rank1
            and door.form == "Mersenne"
        ):
            q3 = q_mod_3(door)
            r = CertResult(
                door=door,
                B=args.B,
                K_cert=28,
                kills=list(KNOWN_RANK1_KILLS),
                qmod3=q3,
                m0_note=m0_desc(q3, door),
                n_primes=len(primes),
                n_active_r=0,
                skipped_qmod0=0,
                wall_s=1.17,
                forb_s=0.0,
                walk_s=0.0,
                reused=True,
            )
            print(
                f"  REUSED K_cert={r.K_cert}  kills={r.n_kills}  "
                f"qmod3={r.qmod3}  compression={r.compression:.3g}",
                flush=True,
            )
        else:
            r = certify(door, primes, args.B, args.k_cap)
            print(
                f"  K_cert={r.K_cert}  kills={r.n_kills}  qmod3={r.qmod3}  "
                f"compression={r.compression:.3g}  "
                f"active_r={r.n_active_r}/{r.n_primes}  skip0={r.skipped_qmod0}",
                flush=True,
            )
            print(
                f"  wall={r.wall_s:.3f}s  (forb {r.forb_s:.3f}s, walk {r.walk_s:.3f}s)  "
                f"{r.survivor_label}  {r.m0_note}",
                flush=True,
            )
            if r.kills:
                preview = ", ".join(
                    f"{k}:{c}:{hit}" for k, c, hit in r.kills[:6]
                )
                more = "" if len(r.kills) <= 6 else f" … +{len(r.kills)-6}"
                print(f"  kills: {preview}{more}", flush=True)
        results.append(r)

    os.makedirs(args.out_dir, exist_ok=True)
    csv_path = os.path.join(args.out_dir, "top100_owner_floor_catalog.csv")
    md_path = os.path.join(args.out_dir, "top100_owner_floor_catalog.md")
    py_src = os.path.join(args.out_dir, "top100_owner_floor_catalog.py")
    source_note = (
        f"PrimePages / t5k.org top 100 from `{os.path.basename(args.t5k)}` "
        f"(fetched Sun Sep 20 2026)."
    )
    tnote = timing_note_rank10()
    takeaway = write_md(md_path, results, args.B, source_note, tnote)
    write_csv(csv_path, results)
    print(f"\nWrote {csv_path}", flush=True)
    print(f"Wrote {md_path}", flush=True)

    # Copy artifacts to microscope
    if args.copy_dir:
        os.makedirs(args.copy_dir, exist_ok=True)
        for src in (csv_path, md_path, py_src):
            if os.path.isfile(src):
                dst = os.path.join(args.copy_dir, os.path.basename(src))
                shutil.copy2(src, dst)
                print(f"Copied → {dst}", flush=True)

    processed = [r for r in results if not r.skipped]
    skipped = [r for r in results if r.skipped]
    by_K = sorted(processed, key=lambda r: (-(r.K_cert or 0), r.door.rank))
    freaks = [r for r in by_K if (r.K_cert or 0) >= 50]

    print("\n--- FREAKS (K>=50) ---", flush=True)
    for r in freaks:
        print(
            f"  #{r.door.rank:3d}  K={r.K_cert:4d}  kills={r.n_kills:3d}  "
            f"comp={r.compression:.3g}  {r.door.form}  {r.door.label}",
            flush=True,
        )
    print(
        f"\nProcessed {len(processed)} / Skipped {len(skipped)} / Total {len(results)}",
        flush=True,
    )
    print("\n--- PASTE-READY ---", flush=True)
    print(takeaway, flush=True)
    print("\n--- TIMING #10 ---", flush=True)
    print(tnote, flush=True)


if __name__ == "__main__":
    main()
