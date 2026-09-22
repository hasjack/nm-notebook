# Zeta denominator / 3-free door safari

Run date: 2026-09-22. Exploratory computation, not a claim of novelty or a prime-size record.

For r=0,...,999999, set k=12r+2 and s=1-k. Compute the exact reduced denominator
D of zeta(s) by the divided-Bernoulli denominator formula:

D = product of p^(1+v_p(k)) over primes p with p-1 dividing k.

For this progression, D has exactly one factor 3 and exactly two factors 2.
All other contributing primes are 11 modulo 12. Set d=D/3. The sole neighbor
not divisible by 3 is q=d+1 if d=1 modulo 3, and q=d-1 otherwise. If prime,
q has 3-free door d. Actual huge Bernoulli numerators are not computed.

## Results

- 1,000,000 inputs, from -1 through -11999989 in steps of -12.
- 172,559 distinct candidates (deduplicated by denominator).
- 151,893 composites.
- 8,096 primes established by deterministic Miller-Rabin below 2^64.
- 12,260 primes with full n-1 Lucas/Pocklington-style certificates.
- 310 probable primes above 2^64, tested at 20 fixed Miller-Rabin bases.
- 653,911 successful input occurrences includes probable primes and repetitions;
  it is not a count of distinct proven primes.

Largest prime found (74 digits):

12831977569478911260230766030673774233497710762579288907341001842771647653

Its source is s=-4754749. Its 3-free door is q-1=D/3.

## Reproduce

Requires Python 3.9+; no third-party packages.

    python safari.py --terms 1000000 --out results-million.json
    python verify.py results-million.json

Results JSON stores large candidate/denominator/door values as decimal strings
to avoid loss of precision in JavaScript. Factor values and certificate witnesses
are small integers. top-ten.json is a convenient shortlist.

## Verification

verify.py independently verifies every saved n-1 certificate, checks its complete
factorization, tests the factor primes by trial division, and checks for each
distinct prime p dividing q-1 a witness a with

    a^(q-1) = 1 mod q
    gcd(a^((q-1)/p)-1, q) = 1.

These conditions force each prime divisor of q to be 1 modulo q-1, proving q prime.
The verifier also checks 100 small even-index denominators against exact Bernoulli
recurrence and reconstructs the denominators of the top ten candidates independently
by enumerating divisors of k.

Completed verification: 12,260 certificates; 100 Bernoulli checks; top 10 denominator
and door checks. This is Python arithmetic verification, not a Lean formalisation.

The deterministic 64-bit Miller-Rabin bases are
2, 325, 9375, 28178, 450775, 9780504, 1795265022.
Above 2^64 the screening bases are the first 20 primes; passing alone is never
reported as proof. Certificates remove that uncertainty for the certified cases.

References:
- https://www.bernoulli.org/ (divided Bernoulli arithmetic)
- https://dlmf.nist.gov/24.10 (Bernoulli arithmetic properties)
- https://cp-algorithms.com/algebra/primality_tests.html (64-bit bases)
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/LucasPrimality.html

Limits: finite exploratory sample, many repeated denominators, no comparison
against a matched random baseline, no demonstrated link to island growth.
