# Door cancellation diagnostic

Run:

    python door_cancellation_lab.py --max 10000000 --out results

Dependencies: numpy, matplotlib. Seed 20261009; 199 conditional shuffles.

Observable: B5(X) = sum over odd primes p !=3 up to X of log(p) times
(1[5 divides m0(p)] - 1[5 divides m1(p)]), where chi3(p)=+1 for p mod3=1,
-1 for p mod3=2; m0=p+chi3 and m1=p-chi3.
Positive residues: 4,11 modulo15. Negative residues: 1,14 modulo15.
The script checks equality of the door and residue definitions at every prime.
This observable uses primes only, rather than all von Mangoldt prime powers.
An independent boolean Eratosthenes sieve reproduced all checkpoint totals;
pi(10^7)=664579.

For each contributing prime, the selected door is whichever is divisible by5.
The factor diagnostics remove every power of2,3,5 before measuring Omega,
distinct factor counts, and largest prime factor. Both-door diagnostics instead
use factors from both m0 and m1 (again excluding2,3,5). Largest-factor bins are
floor(5 log(largest factor)/log(p)), capped at4; Omega bins are capped as
specified in the source.

Gold graph: vertices are odd primes other than3; union p with each odd prime
factor of m0(p). Hub2 is excluded. At each cutoff satellite_active counts
contributing vertices outside the component of5. gold_merge_event marks an
owner whose insertion performs at least two successful unions, joining
previous components. It does not describe every possible definition of a
"bridge" in a final graph.

Controls permute signs within dyadic p-size x p mod3 strata, preserving sign
counts exactly. They illustrate conditional dependence under an artificial
exchangeability model. Arithmetic signs are deterministic functions of
p mod15; the shuffle is not a prime-distribution model. No multiple-testing
adjustment is made, and z scores are descriptive, not proof evidence. Factor
features can encode selection and local divisibility restrictions even after
stripping fixed primes. The forced factor3 in m1 changes cofactor scale.

Findings: large opposite signed factor-bin totals sum to a small global total.
Multiplicity v5 does not separate signs strongly under these controls.
At 10^7 all contributing primes lie in the mainland component, even though
other vertices may remain in satellite components. No new cancellation bound
is established. The dashed sqrt(X) curve is a reference scale, not a theorem
or a fitted asymptotic.

Next: explain largest-factor-bin biases using the exact prime/cofactor
congruences and expected sieve local factors; compare residuals on later
ranges before proposing a bound.
