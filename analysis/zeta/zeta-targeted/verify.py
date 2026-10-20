#!/usr/bin/env python3
"""Independent verifier: python3 verify.py pilot/hits.jsonl

Pocklington uses only factors below 2^64, proved by the Jaeschke
Miller-Rabin bases (isprime64). Their product F must satisfy F^2 > N.
Listed cofactors >= 2^64 are not treated as primes of N.

Denominator origin rebuilds D from the index with three states
(prime | composite | unresolved). Search-fail is unresolved, never omit.
A row verifies only if unresolved == 0 and D matches the receipt.
gmpy2.is_prime is not used as a proof.
"""
import json, sys, math
from origin_audit import LIM, isprime64, modpow, classify_origin, rebuild_denominator

sys.set_int_max_str_digits(0)


def pocklington(n, factors, witnesses):
    """Partial Pocklington: proven 64-bit part F with F^2 > n."""
    proven = {}
    cofactors = {}
    for p, e in factors.items():
        assert isinstance(e, int) and e > 0
        if p < LIM:
            assert isprime64(p)
            proven[p] = e
        else:
            cofactors[p] = e
    assert math.prod(p**e for p, e in factors.items()) == n - 1
    F = math.prod(p**e for p, e in proven.items()) if proven else 1
    assert F * F > n
    R = (n - 1) // F
    assert F * R == n - 1 and math.gcd(F, R) == 1
    for p in proven:
        a = witnesses[str(p)]
        assert modpow(a, n - 1, n) == 1
        assert math.gcd(modpow(a, (n - 1) // p, n) - 1, n) == 1
    return F, proven, cofactors


def validate(row):
    c = row["certificate"]
    n = int(c["n"])
    assert n == int(row["candidate"]) and row["status"] == "certified"
    factors = {int(p): e for p, e in c["factors"].items()}
    F, proven, cofactors = pocklington(n, factors, c["witnesses"])
    k = int(row["index"])
    f = {int(p): e for p, e in row["index_factors"].items()}
    assert k % 12 in (2, 4, 8, 10)
    assert all(isinstance(e, int) and e > 0 and isprime64(p) for p, e in f.items())
    assert math.prod(p**e for p, e in f.items()) == k
    index_primes = tuple(f)
    for p in cofactors:
        assert k % (p - 1) == 0
        state, detail = classify_origin(p, index_primes)
        assert state == "prime", (p, state, detail)

    def _log(msg):
        print(msg, flush=True)

    origin = rebuild_denominator(k, f, progress_every=200, log=_log)
    if origin["unresolved"]:
        sample = origin["unresolved"][:5]
        raise AssertionError(
            "denominator origin unresolved=%d sample=%s counts=%s"
            % (len(origin["unresolved"]), sample, origin["counts"])
        )
    assert origin["D"] == int(row["denominator"]) == 3 * (n - 1)
    assert n % 3 == 2 and int(row["door"]) == n - 1
    assert len(str(n)) == row["digits"]
    return n, proven, cofactors, origin["counts"]


def main():
    if len(sys.argv) < 2:
        print("usage: python3 verify.py hits.jsonl", file=sys.stderr)
        sys.exit(2)
    total = 0
    failed = 0
    for s in open(sys.argv[1]):
        row = json.loads(s)
        if row["status"] != "certified":
            print("UNVERIFIED probable candidate", row.get("candidate"))
            continue
        try:
            n, proven, cofactors, counts = validate(row)
        except AssertionError as e:
            failed += 1
            print("FAIL", row.get("digits"), "digits:", e)
            continue
        total += 1
        msg = "VERIFIED %d digits; zeta input %s; origin %s" % (
            len(str(n)),
            1 - int(row["index"]),
            counts,
        )
        if cofactors:
            msg += "; Pocklington F from %d primes < 2^64; %d cofactors proved from index" % (
                len(proven),
                len(cofactors),
            )
        print(msg)
    print(
        "Verified primality certificates and denominator origins: %d (failed %d)"
        % (total, failed)
    )
    if failed:
        sys.exit(1)


if __name__ == "__main__":
    main()
