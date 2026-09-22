"""Independent certificate verifier. python verify.py results-million.json
No imports from the search script; prime factors checked by trial division.
"""
import json,sys,math
from functools import lru_cache
from fractions import Fraction

@lru_cache(None)
def trial_prime(n):
    return n>=2 and all(n%d for d in range(2,math.isqrt(n)+1))

def denominator_from_divisors(k):
    divisors=set()
    for d in range(1,math.isqrt(k)+1):
        if k%d==0:divisors.update([d,k//d])
    D=1
    for d in divisors:
        p=d+1
        if trial_prime(p):
            D*=p;t=k
            while t%p==0:D*=p;t//=p
    return D

r=json.load(open(sys.argv[1] if len(sys.argv)>1 else 'results-million.json'))
checked=0
for row in r['candidates']:
    if row['status']!='proven-prime-Lucas':continue
    n=int(row['candidate']);c=row['certificate']
    fac={int(p):e for p,e in c['factorization_n_minus_1'].items()}
    assert all(trial_prime(p) and e>=1 for p,e in fac.items())
    assert math.prod(p**e for p,e in fac.items())==n-1
    for p in fac:
        a=c['witnesses'][str(p)]
        assert pow(a,n-1,n)==1
        assert math.gcd(pow(a,(n-1)//p,n)-1,n)==1
    checked+=1
print('Independently verified Lucas certificates:',checked)

# Check the formula against exact Bernoulli recurrence at small indices.
B=[Fraction(1)]
for m in range(1,202):
    B.append(-sum((math.comb(m+1,j)*B[j] for j in range(m)),Fraction(0))/(m+1))
for k in range(2,202,2):assert denominator_from_divisors(k)==(B[k]/k).denominator
print('Exact Bernoulli denominator cross-checks: 100 passed')
top=[x for x in r['candidates'] if x['status']!='composite'][:10]
for row in top:
    k=1-row['first_input']
    assert denominator_from_divisors(k)==int(row['denominator'])
    q=int(row['candidate']);d=int(row['door'])
    assert (q+1 if q%3==1 else q-1)==d
print('Independent denominator and door checks: top 10 passed')
