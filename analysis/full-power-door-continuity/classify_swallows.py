#!/usr/bin/env python3
"""Classify whole-odd-part swallows by m0(r) relative to the old odd block A.

Eligible transitions: consecutive primes, disjoint odd factors, departing
exponent >= 2; through --limit. Among those with A | m0(r) for some arriving
prime factor r of the next door (A = odd part of the departing door, A > 1),
classify each transition once by the cleanest swallow shape:

  clean 2^k A : m0(r) = 2^k * A  (r is a chi3-neighbour of 2^k A)
  messier     : A | m0(r) but the odd part of m0(r) properly exceeds A

Prefer any clean shape over messier. Among clean shapes, prefer the smallest k.
"""
from waits import sieve
from ingredient_transitions import fac
from collections import Counter
from functools import lru_cache
from pathlib import Path
from math import prod
import json, argparse, time


def m0(p):
    return p + (1 if p % 3 == 1 else -1)


def v2_odd(n):
    v = 0
    while n % 2 == 0:
        n //= 2
        v += 1
    return v, n


def fmt_fac(fs):
    parts = []
    for q, e in sorted(fs.items()):
        parts.append(str(q) if e == 1 else f"{q}^{e}")
    return " · ".join(parts) if parts else "1"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--limit", type=int, default=10_000_000)
    X = ap.parse_args().limit
    spf = sieve(X + 1)
    start = time.perf_counter()

    @lru_cache(maxsize=200_000)
    def fs(p):
        return fac(m0(p), spf)

    rows = []
    for p in range(5, X + 1, 2):
        if spf[p]:
            continue
        d = m0(p)
        f = fs(p)
        odd = frozenset(q for q in f if q != 2)
        odd_part = prod(q ** e for q, e in f.items() if q != 2)
        rep = tuple((q, e) for q, e in f.items() if q != 2 and e >= 2)
        arriving = tuple(q for q in f if q != 2)  # odd prime factors of door
        rows.append((p, d, f, odd, odd_part, rep, arriving))
    fs.cache_clear()

    by_k = Counter()
    messier_n = 0
    examples_by_bucket = {}  # key -> list of example dicts (cap later)
    classified = []
    must = {(499, 503), (2801, 2803)}
    must_hits = {}

    for a, b in zip(rows, rows[1:]):
        if a[3] & b[3]:
            continue
        if not a[5]:
            continue
        A = a[4]
        if A <= 1:
            continue
        # Arriving odd prime factors of next door
        swallowers = []
        for r in b[6]:
            mr = m0(r)
            if mr % A != 0:
                continue
            k, odd_r = v2_odd(mr)
            if odd_r == A:
                swallowers.append(("clean", k, r, mr, 1))
            elif odd_r % A == 0:
                extra = odd_r // A
                swallowers.append(("messier", k, r, mr, extra))
            else:
                # A divides mr but not odd_r? Impossible since A odd.
                raise AssertionError((A, r, mr, odd_r))
        if not swallowers:
            continue

        cleans = [s for s in swallowers if s[0] == "clean"]
        if cleans:
            chosen = min(cleans, key=lambda s: (s[1], s[2]))  # smallest k, then r
            shape = "clean"
            k = chosen[1]
            by_k[k] += 1
            bucket = f"2^{k}·A" if k else "2^0·A (=A)"
        else:
            chosen = min(swallowers, key=lambda s: (s[4], s[2]))  # smallest extra
            shape = "messier"
            k = chosen[1]
            messier_n += 1
            bucket = "messier"

        r, mr, extra = chosen[2], chosen[3], chosen[4]
        row = dict(
            previous_prime=a[0],
            prime=b[0],
            previous_door=a[1],
            door=b[1],
            A=A,
            shape=shape,
            k=k if shape == "clean" else None,
            arriving=r,
            arriving_door=mr,
            extra_odd=extra if shape == "messier" else 1,
            old_factors=fmt_fac(a[2]),
            new_factors=fmt_fac(b[2]),
            formula=(
                f"m₀({r}) = {mr} = 2^{k} · {A}"
                if shape == "clean"
                else f"m₀({r}) = {mr} = 2^{v2_odd(mr)[0]} · {A} · {extra}"
            ),
        )
        classified.append(row)
        examples_by_bucket.setdefault(bucket, []).append(row)
        if (a[0], b[0]) in must:
            must_hits[(a[0], b[0])] = row

    n = len(classified)
    # Must match power_continuity whole_odd_part_preserved_repeated
    pc = json.loads((Path(__file__).resolve().parent / "power-continuity.json").read_text())
    expected = pc["counts"]["whole_odd_part_preserved_repeated"]
    assert n == expected, (n, expected)
    assert (499, 503) in must_hits and must_hits[(499, 503)]["shape"] == "clean"
    assert (2801, 2803) in must_hits and must_hits[(2801, 2803)]["shape"] == "clean"
    assert must_hits[(499, 503)]["k"] == 1
    assert must_hits[(2801, 2803)]["k"] == 2

    clean_n = sum(by_k.values())
    assert clean_n + messier_n == n

    # Cap examples per major bucket (prefer must-have rows first)
    example_cap = 5
    examples_out = {}
    for bucket, rows_b in sorted(
        examples_by_bucket.items(),
        key=lambda kv: (0 if kv[0].startswith("2^") else 1, kv[0]),
    ):
        preferred = [
            r
            for r in rows_b
            if (r["previous_prime"], r["prime"]) in must
        ]
        rest = [r for r in rows_b if r not in preferred]
        pick = (preferred + rest)[:example_cap]
        examples_out[bucket] = [
            {
                "previous_prime": r["previous_prime"],
                "prime": r["prime"],
                "previous_door": r["previous_door"],
                "door": r["door"],
                "A": r["A"],
                "arriving": r["arriving"],
                "arriving_door": r["arriving_door"],
                "k": r["k"],
                "extra_odd": r["extra_odd"],
                "old_factors": r["old_factors"],
                "new_factors": r["new_factors"],
                "formula": r["formula"],
            }
            for r in pick
        ]

    by_k_sorted = {str(k): by_k[k] for k in sorted(by_k)}
    shares = {
        **{f"2^{k}·A": dict(count=by_k[k], share=by_k[k] / n) for k in sorted(by_k)},
        "messier": dict(count=messier_n, share=messier_n / n),
    }

    data = dict(
        limit=X,
        seconds=time.perf_counter() - start,
        n=n,
        counts=dict(
            whole_odd_part_preserved_repeated=n,
            clean=clean_n,
            messier=messier_n,
            by_k=by_k_sorted,
        ),
        shares=shares,
        examples=examples_out,
    )
    here = Path(__file__).resolve().parent
    (here / "swallow-shapes.json").write_text(json.dumps(data, indent=2) + "\n")

    lines = [
        "# Swallow shapes for whole-odd-part preservations",
        "",
        f"Among the {n:,} whole-odd-part preservations on the eligible repeated-factor "
        f"slice through {X:,} (consecutive primes, disjoint odd factors, departing "
        f"exponent ≥2; matches `counts.whole_odd_part_preserved_repeated`), classify "
        "each swallow by how `m₀(r)` sits relative to the old odd block `A`.",
        "",
        "Old door of departing prime `p`: `m₀(p)`. Odd part `A = m₀(p) / 2^{v₂(m₀(p))}` "
        "(vacuous `A = 1` excluded). Whole-odd-part preservation: some arriving prime "
        "factor `r` of the next door has `A | m₀(r)`. Clean door-rule shape: "
        "`m₀(r) = 2^k · A` for some `k ≥ 0` (`r` is a χ₃-neighbour of `2^k A`). "
        "Messier leftover: `A | m₀(r)` but the odd part of `m₀(r)` properly exceeds `A`. "
        "One count per transition; prefer any clean shape over messier; among cleans, "
        "prefer smallest `k`.",
        "",
        "## Counts",
        "",
        "| Shape | Count | Share of 1,336 |",
        "|---|---:|---:|",
    ]
    for k in sorted(by_k):
        label = f"m₀(r) = 2^{k} · A"
        lines.append(f"| {label} | {by_k[k]:,} | {by_k[k]/n:.2%} |")
    lines.append(f"| messier (extra odd factors beyond A) | {messier_n:,} | {messier_n/n:.2%} |")
    lines += [
        "",
        f"Clean shapes total {clean_n:,} ({clean_n/n:.2%}); messier {messier_n:,} ({messier_n/n:.2%}). "
        "Clean `2^k A` is door arithmetic (`r = χ₃-neighbour of 2^k A`), not a new adjacency law.",
        "",
        "## Examples",
        "",
    ]
    for bucket, rows_b in examples_out.items():
        lines.append(f"### {bucket}")
        lines.append("")
        lines.append("| Primes | Doors | A | Arriving path |")
        lines.append("|---|---|---:|---|")
        for r in rows_b:
            lines.append(
                f"| {r['previous_prime']} → {r['prime']} | "
                f"{r['previous_door']} → {r['door']} | {r['A']} | "
                f"`{r['formula']}` |"
            )
        lines.append("")
    lines += [
        "## Limits",
        "",
        "Findings only. No predictive law claimed. Pair-level counts; multiple arriving "
        "swallowers count once under the preferred shape. Reproduce: "
        "`python3 classify_swallows.py --limit 10000000`. Independent trial-division "
        "check: `python3 check_swallow_shapes.py`.",
        "",
    ]
    (here / "swallow-shapes.md").write_text("\n".join(lines))
    print(
        json.dumps(
            {
                "n": n,
                "by_k": by_k_sorted,
                "messier": messier_n,
                "clean": clean_n,
                "must": {
                    f"{a}->{b}": must_hits[(a, b)]["formula"] for a, b in must
                },
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
