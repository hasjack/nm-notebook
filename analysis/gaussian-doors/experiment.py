"""Reproduce the finite door experiments. Python standard library only.

Run: python3 experiment.py > results.json
These are integer representation tests, not large-prime certificate checks.
"""
import json
from math import isqrt


def representations(n, coefficient=1):
    """All nonnegative (x,y) with x*x + coefficient*y*y = n."""
    for y in range(isqrt(n // coefficient) + 1):
        x = isqrt(n - coefficient * y * y)
        if x * x + coefficient * y * y == n:
            yield x, y


def primes(limit):
    sieve = bytearray(b'\x01') * (limit + 1)
    sieve[:2] = b'\x00\x00'
    for p in range(2, isqrt(limit) + 1):
        if sieve[p]:
            sieve[p*p:limit+1:p] = b'\x00' * ((limit-p*p)//p+1)
    return [p for p in range(5, limit + 1) if sieve[p]]


def census(limit=100000):
    counts = {r: dict(primes=0, direct=0, door_squares=0, route=0)
              for r in (1, 5, 7, 11)}
    successes = []
    failures = []
    for p in primes(limit):
        chi = 1 if p % 3 == 1 else -1
        door = p + chi
        direct = list(representations(p, 3))
        door_reps = list(representations(door))
        routes = []
        for x, y in door_reps:
            v = y*y - chi
            if v >= 0 and v % 3 == 0:
                b = isqrt(v // 3)
                if 3*b*b == v:
                    routes.append(dict(x=x, y=y, b=b))
        row = counts[p % 12]
        row['primes'] += 1
        row['direct'] += bool(direct)
        row['door_squares'] += bool(door_reps)
        row['route'] += bool(routes)
        if routes:
            successes.append(dict(p=p, door=door, routes=routes))
        elif direct and len(failures) < 10:
            failures.append(dict(p=p, door=door, direct=direct,
                                 door_representations=door_reps))
    return dict(limit=limit, residue_counts=counts,
                successes=successes, example_failures=failures)


def remove_three(limit=10000):
    counts = {key: 0 for key in ('no_to_no', 'no_to_yes',
                                 'yes_to_no', 'yes_to_yes')}
    for door in range(4, limit + 1, 4):
        if door % 3 == 0:
            continue
        n = door - 1 if door % 3 == 1 else door + 1
        stripped = n
        while stripped % 3 == 0:
            stripped //= 3
        before = bool(list(representations(n)))
        after = bool(list(representations(stripped)))
        key = ('yes' if before else 'no') + '_to_' + ('yes' if after else 'no')
        counts[key] += 1
    return dict(limit=limit, tested=sum(counts.values()), counts=counts)


if __name__ == '__main__':
    print(json.dumps(dict(prime_doors=census(), remove_three=remove_three()), indent=2))
