# Exact multiplier local-density check

Run cofactor_local_model.py with numpy, mpmath, matplotlib installed:

    python cofactor_local_model.py --max 10000000 --out output

Every one-factor selected door has d=A*r with r prime>5,
A=2^a3^b5^c, a,c>=1, b>=0. Its owner is p=A*r+epsilon,
epsilon in {-1,+1}. Kept cases have b=0; discarded cases have b>=1.
For b=0, requiring both primes automatically enforces the remaining mod3
condition (apart from excluded tiny primes). For b>=1 the owner mod3 equals
epsilon, as required. The actual decomposition is asserted at every hit.
All admissible A are enumerated, even when there are no observed hits.

At a prime ell, the two linear forms r and A*r+epsilon have one forbidden
residue if ell divides A, and two otherwise. The local correction is
(1-nu/ell)/(1-1/ell)^2. Thus S(A)=2*C2*product_{ell|A,ell>2}
(ell-1)/(ell-2). Here S=8*C2/3 for b=0 and twice that for b>=1.
C2 is approximated by its product over primes <=100000 (no fit to the data).
Weighted pair intensity is S(A) dr/log(r), because the log(p) weight cancels
the prime probability denominator log(p). Prediction integrates from5 to
Y=floor((X-epsilon)/A), using Ei(log(Y))-Ei(log(5)). This is a conjectural
prime-pair model, not a proven density or an error bound.

Predictions are displayed for all cases whose cofactor upper endpoint Y is
at least100,1000,or10000. This condition selects multipliers, not individual
r values; observed data in each case includes all prime r>5. The omitted
signed contribution is included in the JSON. Excluding short ranges avoids
claiming the model is reliable for tiny cofactor populations.

No fitted parameters. Independent comparison with previous factorization run:
one-factor count at10^7 is112285 and signed logarithmic weight is
-137759.1941642142.

The density coefficient at3 doubles when3|A. For a fixed3-free A0,
sum_{b>=1} 2/3^b=1, so the formal leading heuristic coefficients S(A)/A
match between A0 and the discarded family3^b*A0. This identity alone does
not justify summing asymptotics over moving multipliers. The finite-size
logarithmic integrals differ and predict a negative one-factor bias.

Source of heuristic framework: Hardy-Littlewood local prime-pattern models;
see Tao's probabilistic-model lecture notes:
https://terrytao.wordpress.com/2015/01/04/254a-supplement-4-probabilistic-models-and-heuristics-for-the-primes-optional/
