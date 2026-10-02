# FLT proof map

This directory contains checkpoint formalizations of Fermat's Last Theorem for
exponents 3, 4, and 5. The public barrel is `Hire.FLT`; it imports the three
final proof modules and keeps the axiom checks visible.

Final statements:

- `Hire.EisensteinBridge.fermatLastTheoremThree_via_descent :
  FermatLastTheoremFor 3`
- `Hire.fermatLastTheoremFour_via_descent :
  FermatLastTheoremFor 4`
- `Hire.GoldenBridge.fermatLastTheoremFive_via_descent :
  FermatLastTheoremFor 5`

## Module layout

- `Cubic.lean` contains shared cubic arithmetic used by the exponent-3 proof.
- `Experiments.lean` contains exploratory Pythagorean shortfall and mismatch
  identities that are not on the current proof path.
- `Three.lean` contains the Eisenstein-integer descent for exponent 3.
- `Four.lean` contains the classical infinite descent for exponent 4.
- `FivePrelim.lean` contains integer fifth-power factorization lemmas.
- `GoldenRing.lean` contains the golden-ring construction, Euclidean/norm
  machinery, and unit normal forms used for exponent 5.
- `Five.lean` contains the exponent-5 descent.

## Exponent 3

The proof starts from a primitive integer solution to `a^3 + b^3 = c^3`.
The sum-of-cubes factorization separates `a + b` from `cubeFactor a b`.
In the branch `3 | a + b`, coprimality forces the extracted factors to be
`a + b = 9 v^3` and `cubeFactor a b = 3 u^3`.

The Eisenstein argument interprets the factors in the ring of integers of the
third cyclotomic field. After controlling common divisors and units, it
constructs a new primitive cube solution whose output has strictly smaller
`natAbs`. The descent is well-founded on `C.natAbs`.

## Exponent 4

The proof starts from a primitive solution to `a^4 + b^4 = c^4`, rewritten as
`a^4 + b^4 = (c^2)^2`. The Pythagorean parametrization gives coprime
parameters. Their difference and sum are forced to be squares, producing a
second Pythagorean triangle.

The descent constructs a new fourth-power square solution whose hypotenuse has
strictly smaller `natAbs`. Repeating this is impossible by well-foundedness on
`Z.natAbs`, so the original primitive solution cannot exist.

## Exponent 5

The proof starts from a primitive integer solution to `a^5 + b^5 = c^5`.
The integer factorization separates `a + b` from `fifthFactor a b`; residue and
coprimality lemmas control when powers of 5 divide these factors.

The golden-ring argument factors the fifth factor using `phi`, controls common
divisors through `delta = 2*phi - 1`, classifies units up to signed powers of
`phi`, and normalizes associated fifth powers. The proof then treats the
exceptional and parity-sensitive branches through two auxiliary descents:

- `FifthNormSolution` descends on `B.natAbs`; each solution produces another
  solution of the same kind with smaller `B.natAbs`.
- `HalfFifthNormSolution` descends on `Q.natAbs`; each solution produces
  another solution of the same kind with smaller `Q.natAbs`.

Those two well-founded descents rule out the auxiliary norm solutions needed by
the remaining exponent-5 branches.

## Audit notes

- `Hire.FLT` retains `#print axioms` checks for all three final theorems.
- The current trusted axiom footprint is the expected Mathlib baseline:
  `propext`, `Classical.choice`, and `Quot.sound`.
- Exploratory mismatch identities live in `Experiments.lean`; they are useful
  context but not imported by the proof barrel.
