#!/usr/bin/env python3
"""
Cheap-kill experiment: FLT contact with Hire two-door dynamics.
Exploratory only. No paper edits. No zeta in public wording.
"""
from __future__ import annotations

import csv
import math
import time
from collections import Counter, defaultdict
from pathlib import Path

OUT_DIR = Path("/workspace/e-walk-lean/drafts")
R_GERMAIN = 2_000_000
L_LIST = [5, 7, 11, 13, 17, 19, 23, 29, 31]
N_MAX_PRIMDIV = 10**12
A_MAX, B_MAX = 12, 12


def sieve_primes(n: int) -> list[int]:
    if n < 2:
        return []
    bs = bytearray(b"\x01") * (n + 1)
    bs[0:2] = b"\x00\x00"
    for i in range(2, int(n**0.5) + 1):
        if bs[i]:
            step = i
            start = i * i
            bs[start : n + 1 : step] = b"\x00" * ((n - start) // step + 1)
    return [i for i in range(2, n + 1) if bs[i]]


def is_prime(n: int, small_primes: list[int] | None = None) -> bool:
    if n < 2:
        return False
    if n in (2, 3, 5, 7):
        return True
    if n % 2 == 0 or n % 3 == 0 or n % 5 == 0 or n % 7 == 0:
        return False
    if small_primes is not None and n <= (small_primes[-1] if small_primes else 0):
        # binary search not needed; for Germain we use sieve membership
        return False  # caller should use set
    # Miller-Rabin deterministic for 64-bit
    return miller_rabin(n)


def miller_rabin(n: int) -> bool:
    if n < 2:
        return False
    # deterministic bases for n < 2^64
    bases = (2, 3, 5, 7, 11, 13, 23)
    if n in bases:
        return True
    d = n - 1
    s = 0
    while d % 2 == 0:
        d //= 2
        s += 1

    def check(a: int) -> bool:
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            return True
        for _ in range(s - 1):
            x = (x * x) % n
            if x == n - 1:
                return True
        return False

    return all(check(a) for a in bases if a % n != 0)


def m0(p: int) -> int:
    return p + 1 if p % 3 == 1 else p - 1


def m1(p: int) -> int:
    return p - 1 if p % 3 == 1 else p + 1


def door_of_ell(ell: int, r: int) -> str:
    """Where ell lands: m0 / m1 / neither. Expect never neither when ell|(r-1), ell!=2."""
    a, b = m0(r), m1(r)
    on0 = a % ell == 0
    on1 = b % ell == 0
    if on0 and not on1:
        return "m0"
    if on1 and not on0:
        return "m1"
    if on0 and on1:
        return "both"  # only if ell|2r and ell|gcd doors — shouldn't for odd ell
    return "neither"


def valuation_2(n: int) -> int:
    v = 0
    while n % 2 == 0 and n:
        n //= 2
        v += 1
    return v


def odd_prime_factors(n: int) -> list[int]:
    """Return sorted unique odd prime factors of |n|."""
    n = abs(n)
    facs = []
    while n % 2 == 0:
        n //= 2
    f = 3
    while f * f <= n:
        if n % f == 0:
            facs.append(f)
            while n % f == 0:
                n //= f
        f += 2
    if n > 1:
        facs.append(n)
    return facs


def factor_small(n: int) -> list[tuple[int, int]]:
    """Full factorization as (p,e) list for modest n."""
    n = abs(n)
    out = []
    e = 0
    while n % 2 == 0:
        n //= 2
        e += 1
    if e:
        out.append((2, e))
    f = 3
    while f * f <= n:
        e = 0
        while n % f == 0:
            n //= f
            e += 1
        if e:
            out.append((f, e))
        f += 2
    if n > 1:
        out.append((n, 1))
    return out


def motif_sig(ell: int, r: int) -> dict:
    """Small motif signature for door of r."""
    d0, d1 = m0(r), m1(r)
    door = door_of_ell(ell, r)
    door_val = d0 if door == "m0" else (d1 if door == "m1" else 0)
    v2 = valuation_2(door_val) if door_val else -1
    # cofactor after removing 2 and ell from the door ell lands on
    cof = door_val
    if cof:
        while cof % 2 == 0:
            cof //= 2
        while cof % ell == 0:
            cof //= ell
    cof_primes = odd_prime_factors(cof) if cof and cof > 1 else []
    # gold = odd prime factors != 3 of m0
    gold = [p for p in odd_prime_factors(d0) if p != 3]
    sluice_extra = [p for p in odd_prime_factors(d1) if p != 3]  # m1 always has 3
    return {
        "door": door,
        "r_mod3": r % 3,
        "v2_door": v2,
        "exact_2": v2 == 1,
        "cof_primes": tuple(cof_primes[:4]),  # truncate for motif key
        "cof_is_1": cof == 1,
        "gold": tuple(gold[:5]),
        "gold_count": len(gold),
        "ell_on_gold": door == "m0",  # gold arcs use odd primes of m0
    }


def divisors_of(n: int) -> list[int]:
    ds = []
    for i in range(1, int(n**0.5) + 1):
        if n % i == 0:
            ds.append(i)
            if i * i != n:
                ds.append(n // i)
    return sorted(ds)


def is_primitive_divisor_proxy(r: int, a: int, b: int, ell: int) -> bool:
    """
    Cheap proxy: r | (a^ell + b^ell), ell | (r-1), and
    r does not divide a^d + b^d for proper d|ell, d<ell.
    """
    N = pow(a, ell) + pow(b, ell)
    if N % r != 0:
        return False
    if (r - 1) % ell != 0:
        return False
    for d in divisors_of(ell):
        if d == ell:
            continue
        if (pow(a, d) + pow(b, d)) % r == 0:
            return False
    return True


def main() -> None:
    t0 = time.time()
    print(f"Sieving primes up to R={R_GERMAIN}...")
    primes = sieve_primes(R_GERMAIN)
    prime_set = set(primes)
    print(f"  {len(primes)} primes in {time.time()-t0:.2f}s")

    # ---------- 1. Germain auxiliaries ----------
    germain_rows = []
    germain_summary = []
    motif_counter = Counter()
    assert_failures = []
    r_mod3_by_door = Counter()  # (door, r%3) -> count across all ell

    for ell in L_LIST:
        m0_c = m1_c = neither_c = both_c = 0
        r_mod3 = Counter()
        door_by_mod3 = Counter()
        samples = []
        # r = 2*k*ell + 1 <= R
        # k from 1 to (R-1)/(2*ell)
        kmax = (R_GERMAIN - 1) // (2 * ell)
        for k in range(1, kmax + 1):
            r = 2 * k * ell + 1
            if r == 3:
                continue
            if r not in prime_set:
                continue
            # ell | r-1 by construction
            door = door_of_ell(ell, r)
            if door == "neither":
                neither_c += 1
                assert_failures.append((ell, r, "neither"))
            elif door == "both":
                both_c += 1
                assert_failures.append((ell, r, "both"))
            elif door == "m0":
                m0_c += 1
            else:
                m1_c += 1

            rm = r % 3
            r_mod3[rm] += 1
            door_by_mod3[(door, rm)] += 1
            r_mod3_by_door[(door, rm)] += 1

            sig = motif_sig(ell, r)
            # motif key: (ell_door_vs_mod3_rule, v2 exact?, cof pattern class)
            # Expected: m0 iff rm==2, m1 iff rm==1
            expected = "m0" if rm == 2 else ("m1" if rm == 1 else "bad")
            match_expected = door == expected
            motif_key = (
                f"door={door}",
                f"r%3={rm}",
                f"match_mod3={match_expected}",
                f"v2={sig['v2_door']}",
                f"cof1={sig['cof_is_1']}",
                f"gold_n={min(sig['gold_count'], 3)}",
            )
            motif_counter[motif_key] += 1

            if len(samples) < 8:
                samples.append(
                    {
                        "ell": ell,
                        "r": r,
                        "k": k,
                        "door": door,
                        "r_mod3": rm,
                        "m0": m0(r),
                        "m1": m1(r),
                        "v2_door": sig["v2_door"],
                        "cof_primes": ";".join(map(str, sig["cof_primes"])) or "1",
                        "gold": ";".join(map(str, sig["gold"])) or "-",
                        "expected_door": expected,
                        "match": match_expected,
                    }
                )
            germain_rows.append(
                {
                    "source": "germain",
                    "ell": ell,
                    "r": r,
                    "k": k,
                    "door": door,
                    "r_mod3": rm,
                    "m0": m0(r),
                    "m1": m1(r),
                    "v2_door": sig["v2_door"],
                    "exact_2_door": sig["exact_2"],
                    "cof_primes": ";".join(map(str, sig["cof_primes"])) or "1",
                    "gold_primes": ";".join(map(str, sig["gold"])) or "-",
                    "match_mod3_rule": match_expected,
                }
            )

        total = m0_c + m1_c + neither_c + both_c
        germain_summary.append(
            {
                "ell": ell,
                "total_r": total,
                "m0": m0_c,
                "m1": m1_c,
                "neither": neither_c,
                "both": both_c,
                "r_mod3_1": r_mod3[1],
                "r_mod3_2": r_mod3[2],
                "r_mod3_0": r_mod3[0],
                "m0_and_r%3=2": door_by_mod3[("m0", 2)],
                "m1_and_r%3=1": door_by_mod3[("m1", 1)],
                "mismatches": total
                - door_by_mod3[("m0", 2)]
                - door_by_mod3[("m1", 1)],
                "frac_m0": round(m0_c / total, 4) if total else None,
                "frac_m1": round(m1_c / total, 4) if total else None,
            }
        )
        print(
            f"  ell={ell}: total={total} m0={m0_c} m1={m1_c} "
            f"neither={neither_c} mismatches="
            f"{total - door_by_mod3[('m0', 2)] - door_by_mod3[('m1', 1)]}"
        )

    # ---------- 2. Primitive-divisor proxy ----------
    print("Scanning primitive-divisor proxies (a,b <= 12)...")
    prim_rows = []
    prim_summary_by_ell = defaultdict(lambda: Counter())
    seen_r_ell = set()  # avoid double-count same (ell,r) from different (a,b)
    prim_motif = Counter()

    for a in range(1, A_MAX + 1):
        for b in range(1, B_MAX + 1):
            if math.gcd(a, b) != 1:
                continue
            # skip both odd? classical FLT often wants a,b opposite parity for some forms;
            # but a^ell+b^ell for odd ell works for all; keep all coprime pairs
            for ell in L_LIST:
                N = pow(a, ell) + pow(b, ell)
                if N > N_MAX_PRIMDIV or N <= 1:
                    continue
                # factor N (manageable)
                facs = factor_small(N)
                for r, e in facs:
                    if r == 2 or r == 3:
                        continue
                    if not miller_rabin(r):
                        continue
                    if (ell, r) in seen_r_ell:
                        continue
                    if not is_primitive_divisor_proxy(r, a, b, ell):
                        continue
                    seen_r_ell.add((ell, r))
                    door = door_of_ell(ell, r)
                    rm = r % 3
                    expected = "m0" if rm == 2 else ("m1" if rm == 1 else "bad")
                    match = door == expected
                    sig = motif_sig(ell, r)
                    prim_summary_by_ell[ell][door] += 1
                    prim_summary_by_ell[ell][f"r%3={rm}"] += 1
                    prim_summary_by_ell[ell]["total"] += 1
                    if match:
                        prim_summary_by_ell[ell]["match"] += 1
                    else:
                        prim_summary_by_ell[ell]["mismatch"] += 1
                    prim_motif[
                        (
                            f"door={door}",
                            f"r%3={rm}",
                            f"match={match}",
                            f"v2={sig['v2_door']}",
                            f"cof1={sig['cof_is_1']}",
                        )
                    ] += 1
                    prim_rows.append(
                        {
                            "source": "primdiv",
                            "ell": ell,
                            "r": r,
                            "a": a,
                            "b": b,
                            "N": N,
                            "door": door,
                            "r_mod3": rm,
                            "m0": m0(r),
                            "m1": m1(r),
                            "v2_door": sig["v2_door"],
                            "exact_2_door": sig["exact_2"],
                            "cof_primes": ";".join(map(str, sig["cof_primes"])) or "1",
                            "gold_primes": ";".join(map(str, sig["gold"])) or "-",
                            "match_mod3_rule": match,
                        }
                    )

    print(f"  unique (ell,r) primdiv hits: {len(prim_rows)}")

    # ---------- 3. Elementary identity check (all odd primes r<=R) ----------
    # For every odd prime r!=3 with some ell|r-1 from L_LIST, verify rule.
    print("Spot-check: for all primes r<=R, for each ell in L with ell|(r-1)...")
    identity_ok = 0
    identity_bad = 0
    for r in primes:
        if r == 2 or r == 3:
            continue
        for ell in L_LIST:
            if (r - 1) % ell == 0:
                door = door_of_ell(ell, r)
                rm = r % 3
                expected = "m0" if rm == 2 else "m1"
                if door == expected:
                    identity_ok += 1
                else:
                    identity_bad += 1
                    assert_failures.append((ell, r, f"id_fail door={door} rm={rm}"))

    # ---------- Write CSV ----------
    csv_path = OUT_DIR / "flt_two_door_cheap_kill.csv"
    fieldnames = [
        "source",
        "ell",
        "r",
        "k",
        "a",
        "b",
        "N",
        "door",
        "r_mod3",
        "m0",
        "m1",
        "v2_door",
        "exact_2_door",
        "cof_primes",
        "gold_primes",
        "match_mod3_rule",
    ]
    with csv_path.open("w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=fieldnames, extrasaction="ignore")
        w.writeheader()
        for row in germain_rows:
            w.writerow(row)
        for row in prim_rows:
            w.writerow(row)

    # summary CSV too
    summary_csv = OUT_DIR / "flt_two_door_cheap_kill_summary.csv"
    with summary_csv.open("w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(germain_summary[0].keys()))
        w.writeheader()
        for row in germain_summary:
            w.writerow(row)

    # ---------- Motif analysis ----------
    # Top motifs
    top_motifs = motif_counter.most_common(20)
    # Check if ANY mismatch to mod3 rule
    mismatch_motifs = [
        (k, c) for k, c in motif_counter.items() if "match_mod3=False" in k
    ]
    total_germain = sum(s["total_r"] for s in germain_summary)
    total_m0 = sum(s["m0"] for s in germain_summary)
    total_m1 = sum(s["m1"] for s in germain_summary)
    total_mismatch = sum(s["mismatches"] for s in germain_summary)

    # Is there exotic recurring motif beyond mod3?
    # Classify: v2 distribution, cofactor=1 rates by door
    v2_dist = Counter()
    cof1_by_door = Counter()
    for row in germain_rows:
        v2_dist[(row["door"], row["v2_door"])] += 1
        if row["cof_primes"] == "1":
            cof1_by_door[row["door"]] += 1

    # recommendation
    exotic = False
    reason_bits = []
    if total_mismatch == 0 and identity_bad == 0 and not mismatch_motifs:
        reason_bits.append(
            "Door landing is exactly the elementary mod-3 split "
            "(ell|r-1 lands on m0 iff r%3=2, on m1 iff r%3=1)."
        )
    else:
        exotic = True
        reason_bits.append(
            f"UNEXPECTED mismatches: germain={total_mismatch}, identity={identity_bad}."
        )

    # Check if cofactor / v2 patterns suggest forbidden FLT configs
    # Gold-alone erases FLT residue when r%3=1: that's just ell on m1, so not on gold (m0).
    # Recurring "exotic" would be same finite graph motifs forced across ell —
    # we look for motifs that are NOT explained by mod3 + random factorization.
    # Heuristic: if match_mod3 always True and motifs only vary by v2/cof (generic), KILL.
    if not mismatch_motifs and total_mismatch == 0:
        reason_bits.append(
            "Motifs that recur are only the mod-3 door split plus generic "
            "2-adic / cofactor noise; no finite forbidden door pattern forced by "
            "hypothetical FLT solutions appears."
        )
        kill = True
    else:
        kill = False
        reason_bits.append("Recurring mismatch or exotic pattern — KEEP for second look.")

    verdict = "KILL" if kill and not exotic else "KEEP"

    elapsed = time.time() - t0

    # ---------- Markdown report ----------
    md_path = OUT_DIR / "flt_two_door_cheap_kill.md"
    lines = []
    lines.append("# FLT × Hire two-door: cheap-kill experiment")
    lines.append("")
    lines.append("Exploratory draft only. Papers frozen. No public ζ. No Mathlib PR / no push.")
    lines.append("")
    lines.append(f"**Generated:** {time.strftime('%Y-%m-%d %H:%M %Z')}  ")
    lines.append(f"**R (Germain):** {R_GERMAIN:,}  ")
    lines.append(f"**ℓ list:** {L_LIST}  ")
    lines.append(f"**Runtime:** {elapsed:.1f}s")
    lines.append("")
    lines.append("## Room takeaway")
    lines.append("")
    lines.append(f"### **{verdict}**")
    lines.append("")
    lines.append(" ".join(reason_bits))
    lines.append("")
    lines.append(
        "Gold alone erases the FLT residue precisely when the auxiliary sits at "
        "`r ≡ 1 (mod 3)` (then `ℓ | m1`, so `ℓ` is not a gold factor of `m0`). "
        "That is the standing door definition, not a new obstruction."
    )
    lines.append("")
    lines.append("## Door definitions (from `Hire/Doors.lean`)")
    lines.append("")
    lines.append("- `chi3(n)`: +1 if n≡1 mod 3, −1 if n≡2, else 0")
    lines.append("- `m0(p)` = 3-free door: `p+1` if `p%3==1` else `p−1`")
    lines.append("- `m1(p)` = other face (div by 6): `p−1` if `p%3==1` else `p+1`")
    lines.append("- Always `m0+m1=2p`; gold arcs use odd prime factors ≠3 of `m0`")
    lines.append("")
    lines.append("## Elementary identity (DoorOfResidue)")
    lines.append("")
    lines.append(
        "If `ℓ ∣ (r−1)` and `r ≠ 3` is an odd prime, then by definition of `m0`/`m1`:"
    )
    lines.append("")
    lines.append("- `r ≡ 1 (mod 3)` ⇒ `m1(r) = r−1` ⇒ `ℓ ∣ m1` (and `ℓ ∤ m0`)")
    lines.append("- `r ≡ 2 (mod 3)` ⇒ `m0(r) = r−1` ⇒ `ℓ ∣ m0` (and `ℓ ∤ m1`)")
    lines.append("")
    lines.append(
        f"Verified computationally: identity_ok={identity_ok}, identity_bad={identity_bad}, "
        f"Germain mismatches={total_mismatch}, assert_failures={len(assert_failures)}."
    )
    lines.append("")
    lines.append("## 1. Germain auxiliaries `r = 2kℓ+1 ≤ R`")
    lines.append("")
    lines.append(
        f"| ℓ | total r | m0 | m1 | neither | r≡1 | r≡2 | m0∧r≡2 | m1∧r≡1 | mismatches | frac m0 |"
    )
    lines.append(
        "|---:|--------:|---:|---:|--------:|----:|----:|-------:|-------:|-----------:|--------:|"
    )
    for s in germain_summary:
        lines.append(
            f"| {s['ell']} | {s['total_r']} | {s['m0']} | {s['m1']} | {s['neither']} | "
            f"{s['r_mod3_1']} | {s['r_mod3_2']} | {s['m0_and_r%3=2']} | {s['m1_and_r%3=1']} | "
            f"{s['mismatches']} | {s['frac_m0']} |"
        )
    lines.append("")
    lines.append(
        f"**Totals:** Germain hits={total_germain}, m0={total_m0}, m1={total_m1}, "
        f"mismatches={total_mismatch}."
    )
    lines.append("")
    lines.append(
        "Note: `r = 2kℓ+1` with `ℓ` odd ⇒ `r ≡ 1 (mod 2)`; mod-3 distribution of such "
        "primes is not forced 50/50 (depends on `2ℓ mod 3`), so m0/m1 counts need not be equal."
    )
    lines.append("")
    lines.append("### v2 on the door that carries ℓ (Germain)")
    lines.append("")
    lines.append("| door | v2 | count |")
    lines.append("|------|---:|------:|")
    for (door, v2), c in sorted(v2_dist.items()):
        lines.append(f"| {door} | {v2} | {c} |")
    lines.append("")
    lines.append(
        f"Cofactor=1 after stripping 2 and ℓ: m0→{cof1_by_door['m0']}, m1→{cof1_by_door['m1']} "
        f"(of {total_m0}/{total_m1})."
    )
    lines.append("")
    lines.append("## 2. Primitive-divisor proxy")
    lines.append("")
    lines.append(
        f"Scan: a,b ∈ [1..{A_MAX}], gcd=1, N=a^ℓ+b^ℓ ≤ {N_MAX_PRIMDIV:.0e}, "
        "require ℓ∣(r−1) and r ∤ a^d+b^d for proper d∣ℓ."
    )
    lines.append("")
    lines.append("| ℓ | total | m0 | m1 | match mod3 | mismatch |")
    lines.append("|---:|------:|---:|---:|-----------:|---------:|")
    for ell in L_LIST:
        c = prim_summary_by_ell[ell]
        lines.append(
            f"| {ell} | {c['total']} | {c['m0']} | {c['m1']} | {c['match']} | {c['mismatch']} |"
        )
    lines.append("")
    lines.append(f"**Unique (ℓ,r) hits:** {len(prim_rows)}")
    lines.append("")
    lines.append("## 3. Motif search")
    lines.append("")
    lines.append("Top Germain motif keys (door, r%3, match_mod3, v2, cof1, gold_n):")
    lines.append("")
    lines.append("```")
    for k, c in top_motifs:
        lines.append(f"{c:6d}  {k}")
    lines.append("```")
    lines.append("")
    if mismatch_motifs:
        lines.append("**Mismatch motifs (unexpected):**")
        lines.append("```")
        for k, c in mismatch_motifs:
            lines.append(f"{c:6d}  {k}")
        lines.append("```")
    else:
        lines.append(
            "No mismatch motifs. Every Germain and primdiv hit obeys the mod-3 door rule. "
            "Recurring structure is exactly that split; v2/cofactor variation looks generic "
            "(no fixed finite forbidden door graph across ℓ)."
        )
    lines.append("")
    lines.append("## 4. FLT contact reading")
    lines.append("")
    lines.append(
        "- Classical reduction: odd prime exponent ℓ; cyclotomic / Germain auxiliaries "
        "give primes r with ℓ∣(r−1)."
    )
    lines.append(
        "- Hire gold uses odd prime factors ≠3 of **m0**. When the auxiliary has "
        "`r ≡ 1 (mod 3)`, ℓ lands on **m1** (sluice), so gold alone does not see the "
        "FLT residue — expected from door defs, not a new kill criterion beyond mod 3."
    )
    lines.append(
        "- When `r ≡ 2 (mod 3)`, ℓ lands on **m0** (gold-capable). That is again the "
        "definition, not an exotic motif."
    )
    lines.append(
        "- **Conclusion:** nothing computationally special beyond the expected mod-3 "
        "door split; no recurring exotic finite door pattern suggesting a forbidden "
        "configuration forced by hypothetical FLT solutions."
    )
    lines.append("")
    lines.append("## Artifacts")
    lines.append("")
    lines.append(f"- Script: `drafts/flt_two_door_cheap_kill.py`")
    lines.append(f"- CSV (row-level): `drafts/flt_two_door_cheap_kill.csv`")
    lines.append(f"- CSV (summary): `drafts/flt_two_door_cheap_kill_summary.csv`")
    lines.append(f"- This report: `drafts/flt_two_door_cheap_kill.md`")
    lines.append(f"- Lean stub (optional): `Hire/FltTwoDoor.lean`")
    lines.append("")
    lines.append("## Paste-ready takeaway")
    lines.append("")
    lines.append(
        f"**{verdict}.** Germain scan (R={R_GERMAIN:,}, ℓ∈{L_LIST}): "
        f"{total_germain} auxiliaries, door landings m0={total_m0} / m1={total_m1}, "
        f"mismatches vs mod-3 rule = {total_mismatch}; primdiv proxy {len(prim_rows)} hits, "
        f"same exact split. Identity `ℓ∣r−1 ⇒ (ℓ∣m0 ↔ r≡2 mod 3)` holds with "
        f"{identity_ok} checks / {identity_bad} fails. Motifs that recur are only that "
        "split plus generic 2-adic/cofactor noise — no exotic finite door pattern. "
        "Gold erasing FLT residue at r≡1 mod 3 is definitional (ℓ on m1)."
    )
    lines.append("")

    md_path.write_text("\n".join(lines))
    print(f"\nWrote {md_path}")
    print(f"Wrote {csv_path} ({1 + len(germain_rows) + len(prim_rows)} lines)")
    print(f"Wrote {summary_csv}")
    print(f"VERDICT: {verdict}")
    print(f"Elapsed: {elapsed:.1f}s")
    if assert_failures[:5]:
        print("Sample assert failures:", assert_failures[:5])


if __name__ == "__main__":
    main()
