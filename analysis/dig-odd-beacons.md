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

## Hinge dig (continued) — polilog at the peg

At the joint-beacon value z = e^(iπ) = −1 (every spine point with αβln=odd evaluates here):

- π²/6 = −2 Li₂(e^(iπ)) = −2 Li₂(−1)
- 1+1/8+1/27+… = −(4/3) Li₃(e^(iπ)) = −(4/3) Li₃(−1)

So Analysis 2’s two observables sit in one family: polylog order s=2 vs s=3 at the same peg.
The 7/8 odd/even series split is the arithmetic face; Li_s(−1) is the closed face.

This does not invent a new closed form for the cube sum — it places both heights on the peg.
Next dig: deform the argument away from −1 with the three levers and watch Li₂ vs Li₃.

## Analysis 3 — deform off the peg
Route `/analysis-3`: z = base^(α i β π) on the unit circle; watch Li₂(z) vs Li₃(z).
On peg z=−1: −2 Re Li₂ → π²/6 (exits to π); −(4/3) Re Li₃ → cube sum (costume).
Deformation moves both; does not force Li₃(−1) into {e,i,π}.


## Analysis 4 — asymmetric nest

Demand nest = π²/6 only at classical Euler (e,1,1), not on the whole beacon surface.

Along spine base=e^odd with one factor = 1/odd:
- **Symmetric** S=(αβπ ln)^2/6 stays **flat** at π²/6 (product-only).
- **(π ln)^2/6** grows as odd² · π²/6 — moves hard; not a closed-form hint, just the odd label squared.
- **Ignore-α / ignore-β**: with the complementary factor = 1/odd, these become (π)^2/6 or (π odd)^2/6 depending who holds 1/odd — asymmetric in lever choice, still not a cube formula.
- **α² (β π ln)^2/6** and **β² (α π ln)^2/6**: on spine with the 1/odd on that factor, often collapse toward π²/6 again (weight cancels the shrink).
- **α (β π ln)^2/6**: linear leftover of the free factor — varies gently; still probe-grade.

**Star packaging (Jack):** cube sum = −(4/3) Li₃(e^(iπ)), twin of −2 Li₂(e^(iπ)). Prefer over Apéry costume in NM copy.

Honest: asymmetric movement ≠ closed form. e³ is still the same joint peg/nest lock under the symmetric observable.

## Analysis 5 — σ deform polilog

z = base^(σ + α i β π) = base^σ · e^(i π · αβ ln).
Heights: −2 Re Li₂(z), −(4/3) Re Li₃(z).
At σ=0, z=−1: recover π²/6 and cube sum (star costumes).
σ≠0 leaves the unit circle; truncated series needs care for |z|>1.
Expectation from A3: order 2 can still relate to π under angle moves; order 3 does not fall into {e,i,π}. σ is the Magnitude cousin of that question — watch, don’t claim.

## Return / period as unit test

Even prod ⇒ +1 (full turn / return character). Odd prod ⇒ −1 peg.
If a “nest” or height formula uses principal Ln and erases 2π turns, the return test fails (β=2 trap from Analysis 1). Prefer structured exponent for benches.


## Principle — 2 is nature’s only knife (NM)

Jack: the privileged cut is twofold. Maps onto:
- odd vs even prod → −1 peg vs +1 return
- half-turn vs full turn (return = 2 half-turns)
- Li₂ exits to π; Li₃ stays in costume (−(4/3) Li₃(e^(iπ)) exact but no alphabet exit)
- cube sum odd/even denominator split (7/8) — again a 2-power cut

Framing habit, not a proof engine. Prefer noticing where 2 already cuts over inventing higher knives.


## Analysis 5 — continuation past |z|=1

Knife: |z|=1 is the series fence (twofold: inside / outside).

Inversion (principal Ln):
- Li₂(z) = −Li₂(1/z) − π²/6 − ½[Ln(−z)]²
- Li₃(z) = Li₃(1/z) − (π²/6)Ln(−z) − ⅙[Ln(−z)]³

At Euler + σ=0.25: |z|≈1.28, continued heights finite (e.g. −(4/3)Re Li₃ ≈ 1.51, not cube; −2 Re Li₂ ≈ 2.02, not π²/6). Continuation ≠ alphabet exit.
