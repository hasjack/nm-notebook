"""Exact denominator search; standard library only. python safari.py --terms 100000

For k=12r+2, denominator(zeta(1-k)) = 12 * product p^(1+v_p(k)),
over primes p>3 with p-1 dividing k. These primes are 11 mod 12.
Output candidate is the sole neighbor of D/3 not divisible by 3.
Miller-Rabin is deterministic below 2^64 using the seven documented bases;
above that cutoff, passing the listed fixed bases means PROBABLE, not proven.
For q=d+1 a Lucas n-1 certificate proves primality using the complete known
factorization of d and separate witnesses for its distinct prime factors.
"""
import argparse,json,math,time
from pathlib import Path

def prime_sieve(limit):
    s=bytearray(b'\1')*(limit+1);s[:2]=b'\0\0'
    for p in range(2,math.isqrt(limit)+1):
        if s[p]:s[p*p::p]=b'\0'*((limit-p*p)//p+1)
    return s

def passes_mr(n,bases):
    if n<2:return False
    if n%2==0:return n==2
    d=n-1;s=0
    while d%2==0:d//=2;s+=1
    for a in bases:
        a%=n
        if a==0:continue
        x=pow(a,d,n)
        if x in (1,n-1):continue
        for _ in range(s-1):
            x=x*x%n
            if x==n-1:break
        else:return False
    return True

BASES64=[2,325,9375,28178,450775,9780504,1795265022]
BASESBIG=[2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71]

def lucas_certificate(q,factors):
    if math.prod(p**e for p,e in factors.items())!=q-1:return None
    witnesses={}
    for p in factors:
        for a in range(2,502):
            if pow(a,q-1,q)==1 and math.gcd(pow(a,(q-1)//p,q)-1,q)==1:
                witnesses[p]=a;break
        else:return None
    return {'factorization_n_minus_1':factors,'witnesses':witnesses}

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--terms',type=int,default=100000)
    parser.add_argument('--out',default='results.json');a=parser.parse_args()
    assert a.terms>0
    start=time.time();maximum=12*(a.terms-1)+2
    sieve=prime_sieve(max(1000,maximum//5+1))
    denominators=[12]*a.terms;factorlists=[{} for _ in range(a.terms)]
    for p in range(11,maximum//5+2,12):
        if not sieve[p]:continue
        for k in range(5*(p-1),maximum+1,6*(p-1)):
            r=(k-2)//12;e=1;t=k
            while t%p==0:e+=1;t//=p
            denominators[r]*=p**e;factorlists[r][p]=e
    unique={}
    for r,D in enumerate(denominators):
        if D in unique:unique[D]['occurrences']+=1;continue
        d=D//3;q=d+(1 if d%3==1 else -1)
        assert d%4==0 and d%3!=0 and q%3!=0
        f={2:2,**factorlists[r]}
        assert math.prod(p**e for p,e in f.items())==d
        row={'first_input':-(12*r+1),'denominator':str(D),'door':str(d),
             'candidate':str(q),'digits':len(str(q)),'occurrences':1,
             'door_factors':f,'status':'composite'}
        small=next((p for p in range(2,1000) if sieve[p] and q!=p and q%p==0),None)
        if small:row['small_factor']=small
        elif passes_mr(q,BASES64 if q<2**64 else BASESBIG):
            row['status']='proven-prime-64bit' if q<2**64 else 'probable-prime'
            if q==d+1:
                cert=lucas_certificate(q,f)
                if cert:row['status']='proven-prime-Lucas';row['certificate']=cert
        unique[D]=row
    ordered=sorted(unique.values(),key=lambda r:int(r['candidate']),reverse=True)
    counts={status:sum(r['status']==status for r in ordered) for status in
            ['composite','proven-prime-64bit','proven-prime-Lucas','probable-prime']}
    result={'terms':a.terms,'last_input':-(12*(a.terms-1)+1),
            'distinct':len(ordered),'counts':counts,
            'successful_terms':sum(r['occurrences'] for r in ordered if r['status']!='composite'),
            'miller_rabin_bases_64':BASES64,'miller_rabin_bases_big':BASESBIG,
            'seconds':round(time.time()-start,2),'candidates':ordered}
    Path(a.out).write_text(json.dumps(result,indent=2))
    print(json.dumps({k:v for k,v in result.items() if k!='candidates'},indent=2))
    print('Largest successful candidates:')
    print(json.dumps([r for r in ordered if r['status']!='composite'][:8],indent=2))
    print('Largest candidate overall:',ordered[0])

if __name__=='__main__':main()
