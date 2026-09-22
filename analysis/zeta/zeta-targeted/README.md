# Targeted zeta-door experiment

gmpy2 for large Q and for d+1 when k ≥ 2^64. Kitchen record: 5522-digit
certified plus-side neighbour (kitchen8/). Hunt first, prove later:

    python3 hunt.py --no-cert --min-digits 3400 --max-digits 10000 \
      --pool-max 71 --nmin 8 --nmax 8 --emin 2 --emax 2 \
      --out kitchen-next
    python3 cert.py kitchen-next/hits.jsonl          # longest hit only
    python3 cert.py --all kitchen-next/hits.jsonl    # every hit
    python3 verify.py kitchen-next/hits.certified.jsonl

Python 3.9+ otherwise. Unzip, open a terminal in this folder.

## Run a five-minute, 100-300 digit experiment

    python3 hunt.py --seconds 300 --attempts 10000 --out run100
    python3 verify.py run100/hits.jsonl

The run ends at the time budget OR the attempt count, whichever comes first.
Time is checked between attempts, so a single calculation can exceed the budget.
Each run's --attempts means additional attempts. Repeat the same command to resume.
Ctrl-C stops safely after preserving completed attempts. An interrupted candidate
may be repeated. All completed outcomes, including composites, are recorded.
Use separate output directories for simultaneous processes; no shared-file locking.

## Larger digit bands

    python3 hunt.py --seconds 300 --attempts 10000 --min-digits 300 --max-digits 1000 --out run300
    python3 verify.py run300/hits.jsonl

    python3 hunt.py --seconds 600 --attempts 20000 --min-digits 1000 --max-digits 3200 --out run1000
    python3 verify.py run1000/hits.jsonl

These are target bands, not promises of prime hits. The index family is finite;
duplicates become common on extended runs. This is a bounded pilot, not an
unlimited record-search engine. Changing --seed requires a fresh --out directory.

## Construction

Build fully factored k from 2 and five to seven primes selected from
5,7,11,13,17,19,23,29,31, with odd-prime exponents one or two.
Adjust the exponent of 5 if necessary to ensure k=2 modulo 12.
The experiment takes the exact reduced denominator D of zeta(1-k), removes
its one factor of 3, and chooses the sole neighbor Q of d=D/3 not divisible by 3.

D = product p^(1+v_p(k)) over ALL primes p with p-1 dividing k.

All divisors of k are enumerated: no selected factors are silently omitted.
This is a genuine denominator construction, not an arbitrary product inspired by it.
k may exceed 2^64 when gmpy2 is installed (d+1 tested with gmpy2.is_prime).
Without gmpy2, factor primes must stay in the 64-bit deterministic MR range.

## Screening and proof

Only Q=d+1 is tested in this pilot, giving a complete known factorization of Q-1.
Minus-side candidates are logged as deferred, not as composites.
After deduplication and digit-band filtering, sieve by primes below 10000,
then run 12 fixed-base Miller-Rabin screens. Passing those screens alone is
only probable primality. A hit becomes certified only after constructing an
exact full-factorization n-1 certificate. All certificates are independently
rechecked by verify.py, which also rebuilds their exact zeta denominators.
This is arithmetic verification in Python, not a Lean proof.

For each prime factor p of Q-1, the certificate supplies a witness a satisfying
a^(Q-1)=1 modulo Q and gcd(a^((Q-1)/p)-1,Q)=1. These conditions force every
prime divisor of Q to be 1 modulo Q-1, proving Q prime. All factor primes
are independently checked within the deterministic 64-bit range.

Numbers of arbitrary size are stored as decimal strings. Do not load them as
JavaScript floating-point Numbers. Factor bases are at most 64 bits and appear
as string dictionary keys; exponents and witnesses are small integers.

## Files

- hunt.py: search, deterministic seed, checkpoints, stage timing. --no-cert skips Pocklington.
- cert.py: prove probable hits from a hits.jsonl.
- verify.py: independent certificate and denominator-origin verifier.
- selftest.py: exact Bernoulli small cases, primality checks, corrupted-data
  rejection and resume regression. Run from this folder: python3 selftest.py
- pilot/: completed example run and verification output.

The supplied pilot logged 12000 attempts, including 5320 repeated indices.
It generated seven certified primes of lengths 118,121,121,123,129,215,245.
All seven passed the separate verifier. This is not a comparison against farm.py,
and no speed advantage or novelty is claimed. Generation/test timings exclude
some I/O, setup, and verification costs; use total wall time for comparisons.

## Your PARI/GP certificate

The supplied champ2518.cert has the shape documented for PARI ECPP certificates:
a vector of 260 five-entry vectors, with a 2518-digit first N.
Format inspection alone is not certificate validation. GP was not installed
in the environment used for this pilot. To validate with PARI/GP, start gp in
the directory containing that certificate and enter:

    c = read("champ2518.cert");
    primecertisvalid(c)

A result of 1 means the certificate verifies. The certificate is not duplicated
in this bundle; use your original file.

References:
https://pari.math.u-bordeaux.fr/dochtml/ref/Arithmetic_functions.html#primecertisvalid
https://www.bernoulli.org/
https://cp-algorithms.com/algebra/primality_tests.html

