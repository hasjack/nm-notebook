#!/usr/bin/env python3
"""Independent verifier: python3 verify.py pilot/hits.jsonl

Pocklington uses only factors below 2^64, proved by the Jaeschke
Miller-Rabin bases (isprime64). Their product F must satisfy F^2 > N.
Listed cofactors >= 2^64 are not treated as primes of N.

Denominator origin rebuilds D from the index. Von Staudt primes below
2^64 are proved by isprime64. Any p = d+1 >= 2^64 is proved by Pocklington
on p-1, which divides the fully factored index (all index primes < 2^64).
gmpy2.is_prime is not used as a proof.
"""
import json,sys,math
from functools import lru_cache

sys.set_int_max_str_digits(0)

LIM=2**64

try:
    import gmpy2
    def modpow(a,e,m):
        return int(gmpy2.powmod(int(a),int(e),int(m)))
except ImportError:
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

def factor_over(n,primes):
    out={};t=n
    for p in primes:
        e=0
        while t%p==0:t//=p;e+=1
        if e:out[p]=e
    return out,t

def pocklington_from_index(n,index_primes):
    """Prove n prime when n-1 factors over 64-bit index primes."""
    factors,rest=factor_over(n-1,index_primes)
    if rest!=1 or not factors:return False
    assert all(isprime64(p) for p in factors)
    F=n-1
    if F*F<=n:return False
    for p in factors:
        for a in range(2,502):
            if modpow(a,n-1,n)==1 and math.gcd(modpow(a,(n-1)//p,n)-1,n)==1:
                break
        else:
            return False
    return True

def origin_prime(n,index_primes):
    n=int(n)
    if n<LIM:return isprime64(n)
    return pocklington_from_index(n,index_primes)

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
    assert k%12 in (2,4,8,10)
    assert all(isinstance(e,int) and e>0 and isprime64(p) for p,e in f.items())
    assert math.prod(p**e for p,e in f.items())==k
    index_primes=tuple(f)
    for p in cofactors:
        assert k%(p-1)==0
        assert pocklington_from_index(p,index_primes)
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
        if origin_prime(p,index_primes):
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
            msg+='; Pocklington F from %d primes < 2^64; %d cofactors proved from index'%(
                len(proven),len(cofactors))
        print(msg)
    print('Verified primality certificates and denominator origins:',total)

if __name__=='__main__':main()
