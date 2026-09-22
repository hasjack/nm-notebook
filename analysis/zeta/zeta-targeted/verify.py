#!/usr/bin/env python3
"""Independent verifier: python3 verify.py pilot/hits.jsonl
Verifies certificate AND exact zeta-denominator origin. Does not import hunt.py.
"""
import json,sys,math
from functools import lru_cache

@lru_cache(maxsize=100000)
def isprime64(n):
    if not 2<=n<2**64:return False
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

def validate(row):
    c=row['certificate'];n=int(c['n'])
    assert n==int(row['candidate']) and row['status']=='certified'
    factors={int(p):e for p,e in c['factors'].items()}
    assert all(isinstance(e,int) and e>0 and isprime64(p) for p,e in factors.items())
    assert math.prod(p**e for p,e in factors.items())==n-1
    for p in factors:
        a=c['witnesses'][str(p)]
        assert pow(a,n-1,n)==1
        assert math.gcd(pow(a,(n-1)//p,n)-1,n)==1
    k=int(row['index']);f={int(p):e for p,e in row['index_factors'].items()}
    assert k%12==2 and k<2**64-1
    assert all(isinstance(e,int) and e>0 and isprime64(p) for p,e in f.items())
    assert math.prod(p**e for p,e in f.items())==k
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
        if isprime64(p):
            D*=p;t=k
            while t%p==0:D*=p;t//=p
    assert D==int(row['denominator'])==3*(n-1)
    assert n%3==2 and int(row['door'])==n-1
    assert len(str(n))==row['digits']
    return n

def main():
    total=0
    for s in open(sys.argv[1]):
        row=json.loads(s)
        if row['status']!='certified':
            print('UNVERIFIED probable candidate',row['candidate']);continue
        n=validate(row);total+=1
        print('VERIFIED',len(str(n)),'digits; zeta input',1-int(row['index']))
    print('Verified certificates and denominator origins:',total)

if __name__=='__main__':main()
