# Dig notes — beacons vs odd reciprocal-power sums

## Constraint (hard)
If the structured nest must equal π²/6 on the **entire** analytical-beacon surface
`α·β·ln(base)=±1`, then the nest can only depend on that product (up to sign).
Proof sketch: trades α↔β and base↔β along the surface leave prod fixed; any continuous
observable constant on the surface is constant on those trades, hence product-only
among the usual monomials α^p β^q ln^r with weight fixed by classical calibration.

**Consequence:** e³ and e⁵ are **not** independent nest beacons. They are the same
nest lock, seen at different lever angles. Full-beacon green cannot by itself open
a new formula for 1+1/8+1/27+….

## What e³ / e⁵ *do* mark
With α=1, base=e^9, β=1/odd:
- joint lock: −1 peg **and** π²/6 nest
- odd ∈ {1,3,5,…} is required by the peg, not by the square sum

Even powers e²,e⁴ keep nest=π²/6 but peg +1 (decoys for the joint lock).

## Second probe (the real dig)
Keep nest as the even calibrator (product-only). Add a **spine probe** that varies
on e, e³, e⁵ while nest stays fixed.

Structural rhyme found:
- peg lattice odds {1,3,5,…}
- cube sum splits into odd-denominator and even-denominator terms
- sum_{n odd} 1/n³ = (7/8) · (1+1/8+1/27+…)

So the same odd integers that label joint beacons also label the odd-denominator
part of the cube sum. That is a hinge, not a closed form.

## Naive π³/c
c = π³ / (cube sum) ≈ 25.794350 — not a small integer.
π³/26 ≈ 1.192549 vs cube ≈ 1.202057 (close, not equal).

## Next cracks to try
1. Two-observable lock: nest(prod)=π²/6 AND probe(spine)=F(odds) related to cube split (7/8).
2. Don’t demand nest green on full surface — only classical; allow asymmetric nest; use e³ as independent.
3. Polylog / Fourier angles that reduce to nest at s=2 and stay defined at s=3.

## Analysis 2 bench
Route `/analysis-2`: two-observable lock.
- A: structured nest on spine (flat) + −1 peg
- B: odd/even split of cube reciprocal sum → ratio → 7/8
