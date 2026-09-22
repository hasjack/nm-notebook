#!/usr/bin/env python3
"""Independent verifier: python3 verify.py pilot/hits.jsonl

Pocklington uses only factors below 2^64, proved by the Jaeschke
Miller-Rabin bases (isprime64). Their product F must satisfy F^2 > N.
Listed cofactors >= 2^64 are not treated as primes.

Denominator origin rebuilds D from the index. Von Staudt primes below
2^64 are proved; any p = d+1 >= 2^64 is a gmpy2 probable prime, not a proof.
"""
import json,sys,math
from functools import lru_cache

sys.set_int_max_str_digits(0)

LIM=2**64

try:
    import gmpy2
    def prp(n):
        n=int(n)
        return n>=2 and bool(gmpy2.is_prime(n))
    def modpow(a,e,m):
        return int(gmpy2.powmod(int(a),int(e),int(m)))
except ImportError:
    def prp(n):
        return isprime64(n)
    def modpow(a,e,m):
        return pow(int(a),int(e),int(m))

@lru_cache(maxsize=100000)
def isprime64(n):
    if not 2<=n<LIM:return False
    if n%2==0:return n==2
    odd=n-1;power=0
    while not odd%2:odd//=2;power+=1
    for a in [2,325,9375,28178,450775,9780504,1795265022]:
        if a%n==0:continue
        v=pow(a,odd,n)
        for j in range(power):
            if v==n-1 or (j==0 and v==1):break
            v=v*v%n
        else:return False
    return True

def origin_prime(n):
    n=int(n)
    if n<LIM:return isprime64(n)
    return prp(n)

def pocklington(n,factors,witnesses):
    """Partial Pocklington: proven 64-bit part F with F^2 > n."""
    proven={};cofactors={}
    for p,e in factors.items():
        assert isinstance(e,int) and e>0
        if p<LIM:
            assert isprime64(p)
            proven[p]=e
        else:
            cofactors[p]=e
    assert math.prod(p**e for p,e in factors.items())==n-1
    F=math.prod(p**e for p,e in proven.items()) if proven else 1
    assert F*F>n
    R=(n-1)//F
    assert F*R==n-1 and math.gcd(F,R)==1
    for p in proven:
        a=witnesses[str(p)]
        assert modpow(a,n-1,n)==1
        assert math.gcd(modpow(a,(n-1)//p,n)-1,n)==1
    return F,proven,cofactors

def validate(row):
    c=row['certificate'];n=int(c['n'])
    assert n==int(row['candidate']) and row['status']=='certified'
    factors={int(p):e for p,e in c['factors'].items()}
    F,proven,cofactors=pocklington(n,factors,c['witnesses'])
    k=int(row['index']);f={int(p):e for p,e in row['index_factors'].items()}
    assert k%12==2
    assert all(isinstance(e,int) and e>0 and isprime64(p) for p,e in f.items())
    assert math.prod(p**e for p,e in f.items())==k
    for p in cofactors:
        assert k%(p-1)==0
    # Independently enumerate all index divisors, testing all potential p=d+1.
    ds={1}
    for p,e in f.items():
        expanded=set()
        for d in ds:
            t=d
            for _ in range(e+1):expanded.add(t);t*=p
        ds=expanded
    D=1
    for d in ds:
        p=d+1
        if origin_prime(p):
            D*=p;t=k
            while t%p==0:D*=p;t//=p
    assert D==int(row['denominator'])==3*(n-1)
    assert n%3==2 and int(row['door'])==n-1
    assert len(str(n))==row['digits']
    return n,proven,cofactors

def main():
    total=0
    for s in open(sys.argv[1]):
        row=json.loads(s)
        if row['status']!='certified':
            print('UNVERIFIED probable candidate',row['candidate']);continue
        n,proven,cofactors=validate(row);total+=1
        msg='VERIFIED %d digits; zeta input %s'%(len(str(n)),1-int(row['index']))
        if cofactors:
            msg+='; Pocklington F from %d primes < 2^64 (%d cofactors unproven)'%(
                len(proven),len(cofactors))
        print(msg)
    print('Verified certificates and denominator origins:',total)

if __name__=='__main__':main()
