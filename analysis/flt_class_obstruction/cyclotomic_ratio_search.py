#!/usr/bin/env python3
"""Finite-field screens for the cyclotomic-ratio lab note.

This is an exploratory check, not an FLT proof.  It tests ordered coprime
positive pairs a,b <= 20 against two necessary-looking conditions:

* a+b and F_p(a,b) = (a^p+b^p)/(a+b) are p-th powers away from p;
* the linked conjugate-ratio exponents seen in finite fields satisfy the
  linear pattern forced by an element-power representation.

The second condition is conditional on principality/element powers.  A vanished
tested reduction is reported as undecided rather than as a pass.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import gcd
from typing import Iterable

from sympy import factorint


@dataclass(frozen=True)
class Suite:
    p: int
    fields: tuple[int, ...]
    vanish_policy: str


SUITES = (
    Suite(7, (29, 43), "alternate_field_may_reject"),
    Suite(37, (149, 223), "ordered_stop"),
)


def factor(n: int) -> dict[int, int]:
    return {int(q): int(e) for q, e in factorint(n).items()}


def is_pth_power_away_from_p(n: int, p: int) -> bool:
    return all(q == p or e % p == 0 for q, e in factor(n).items())


def fermat_cofactor(a: int, b: int, p: int) -> int:
    return (a**p + b**p) // (a + b)


def valuation_passes(a: int, b: int, p: int) -> bool:
    return is_pth_power_away_from_p(a + b, p) and is_pth_power_away_from_p(
        fermat_cofactor(a, b, p), p
    )


def primitive_root(ell: int) -> int:
    phi = ell - 1
    primes = tuple(factor(phi))
    for g in range(2, ell):
        if all(pow(g, phi // q, ell) != 1 for q in primes):
            return g
    raise ValueError(f"no primitive root found for {ell}")


def inv(x: int, ell: int) -> int:
    return pow(x, -1, ell)


def field_ratio_result(a: int, b: int, p: int, ell: int) -> str:
    """Return pass/reject/vanish for j = 1,2,3 in F_ell.

    For ell = 1 mod p, write F_ell^* = <g> and zeta = g^((ell-1)/p).
    The quotient by p-th powers identifies a conjugate ratio with an exponent
    t mod p.  The linked screen asks whether t_j = j*t_1 for j = 1,2,3.
    """

    g = primitive_root(ell)
    step = (ell - 1) // p
    zeta = pow(g, step, ell)
    step_inv = inv(step % p, p)

    logs: dict[int, int] = {}
    x = 1
    for exponent in range(ell - 1):
        logs[x] = exponent
        x = (x * g) % ell

    linked: list[tuple[int, int]] = []
    for j in (1, 2, 3):
        numerator = (a + b * pow(zeta, j, ell)) % ell
        denominator = (a + b * pow(zeta, p - j, ell)) % ell
        if numerator == 0 or denominator == 0:
            return "vanish"

        ratio = numerator * inv(denominator, ell) % ell
        t = logs[ratio] * step_inv % p
        linked.append((j, t))

    t1 = linked[0][1]
    if all(t == (j * t1) % p for j, t in linked):
        return "pass"
    return "reject"


def linked_result(a: int, b: int, suite: Suite) -> str:
    if suite.vanish_policy == "ordered_stop":
        saw_pass = False
        for ell in suite.fields:
            result = field_ratio_result(a, b, suite.p, ell)
            if result == "vanish":
                return "undecided"
            if result == "reject":
                return "rejected"
            saw_pass = True
        return "passed" if saw_pass else "undecided"

    field_results = [field_ratio_result(a, b, suite.p, ell) for ell in suite.fields]
    if "reject" in field_results:
        return "rejected"
    if all(r == "pass" for r in field_results):
        return "passed"
    return "undecided"


def pairs(bound: int = 20) -> Iterable[tuple[int, int]]:
    for a in range(1, bound + 1):
        for b in range(1, bound + 1):
            if gcd(a, b) == 1:
                yield a, b


def main() -> None:
    sample = tuple(pairs())
    print(f"ordered coprime positive pairs a,b <= 20: {len(sample)}")
    print()
    print("| Test | p=7 | p=37 |")
    print("| --- | ---: | ---: |")

    valuation_counts = {
        suite.p: sum(1 for a, b in sample if valuation_passes(a, b, suite.p))
        for suite in SUITES
    }
    print(
        "| Both a+b and F_p(a,b) are p-th powers away from p | "
        f"{valuation_counts[7]} | {valuation_counts[37]} |"
    )

    rows: dict[int, dict[str, int]] = {}
    survivors: dict[int, list[tuple[int, int]]] = {}
    for suite in SUITES:
        counts = {"rejected": 0, "undecided": 0, "passed": 0}
        survivors[suite.p] = []
        for a, b in sample:
            result = linked_result(a, b, suite)
            counts[result] += 1
            if result == "passed":
                survivors[suite.p].append((a, b))
        rows[suite.p] = counts

    print(
        "| Rejected by conditional linked conjugate-ratio test | "
        f"{rows[7]['rejected']} | {rows[37]['rejected']} |"
    )
    print(
        "| Undecided because a tested reduction vanished | "
        f"{rows[7]['undecided']} | {rows[37]['undecided']} |"
    )
    print(
        "| Passed linked test | "
        f"{rows[7]['passed']} | {rows[37]['passed']} |"
    )
    print()
    print(f"p=7 linked-test survivors: {survivors[7]}")
    print(f"p=37 linked-test survivors: {survivors[37]}")
    print("for (1,1), (1+zeta)/(1+zeta^-1) = zeta")


if __name__ == "__main__":
    main()
