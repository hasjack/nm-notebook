#!/usr/bin/env python3
"""Target exact zeta denominators; standard-library Python 3.9+.
python3 hunt.py --seconds 300 --attempts 10000
python3 verify.py results/hits.jsonl
"""
import argparse, json, math, random, sys, time
from pathlib import Path
from functools import lru_cache

sys.set_int_max_str_digits(0)

BASES64=(2,325,9375,28178,450775,9780504,1795265022)
BASES=(2,3,5,7,11,13,17,19,23,29,31,37)
POOL=(5,7,11,13,17,19,23,29,31)
LIMIT=2**64-1
MAX_DIV=200000
# Even k, 3 does not divide k. Tight family is k ≡ 2 (mod 12).
MOD12_OK=(2,4,8,10)

try:
    import gmpy2
    def is_prime(n):
        n=int(n)
        return n>=2 and bool(gmpy2.is_prime(n))
    def modpow(a,e,m):
        return int(gmpy2.powmod(int(a),int(e),int(m)))
    ENGINE='gmpy2'
except ImportError:
    def is_prime(n):
        n=int(n)
        if n<2:return False
        if n>=LIMIT:raise ValueError('gmpy2 required for primes >= 2^64')
        return mr(n,BASES64)
    def modpow(a,e,m):
        return pow(int(a),int(e),int(m))
    ENGINE='stdlib'

def odd_primes_upto(n):
    s=bytearray(b'\1')*(n+1);s[:2]=b'\0\0'
    for p in range(2,int(n**0.5)+1):
        if s[p]:s[p*p::p]=b'\0'*((n-p*p)//p+1)
    return tuple(p for p in range(5,n+1) if s[p])

def mr(n,bases):
    if n<2:return False
    if n%2==0:return n==2
    d=n-1;s=0
    while d%2==0:d//=2;s+=1
    for base in bases:
        if base%n==0:continue
        x=pow(base,d,n)
        if x in (1,n-1):continue
        for _ in range(s-1):
            x=x*x%n
            if x==n-1:break
        else:return False
    return True

@lru_cache(maxsize=200000)
def prime64(n):
    if not 0<=n<2**64:raise ValueError('Factor exceeds exact 64-bit primality range')
    return mr(n,BASES64)

def divisors(f):
    ds=[1]
    for p,e in f.items():ds=[d*p**a for d in ds for a in range(e+1)]
    return ds

def divisor_count(f):
    n=1
    for e in f.values():n*=e+1
    return n

def denominator(f):
    k=math.prod(p**e for p,e in f.items())
    assert k%12 in MOD12_OK
    if divisor_count(f)>MAX_DIV:
        raise ValueError('too many divisors')
    factors={}
    for d in divisors(f):
        p=d+1
        if is_prime(p):
            e=1;t=k
            while t%p==0:t//=p;e+=1
            factors[p]=e
    assert factors.pop(3)==1
    return k,math.prod(p**e for p,e in factors.items()),factors

def index_for(i,seed,pool,nmin,nmax,emin,emax,vmin2=1,vmax2=1,force_mod12=2):
    rng=random.Random(seed+i)
    nmin=max(1,min(nmin,len(pool))); nmax=max(nmin,min(nmax,len(pool)))
    emin=max(1,emin); emax=max(emin,emax)
    vmin2=max(1,vmin2); vmax2=max(vmin2,vmax2)
    for _ in range(80):
        chosen=rng.sample(pool,rng.randint(nmin,nmax))
        f={2:rng.randint(vmin2,vmax2),**{p:rng.randint(emin,emax) for p in chosen}}
        k=math.prod(p**e for p,e in f.items())
        if force_mod12 is not None and k%12!=force_mod12:
            f[5]=f.get(5,0)+1
            k=math.prod(p**e for p,e in f.items())
        if k%12 not in MOD12_OK:
            continue
        if force_mod12 is not None and k%12!=force_mod12:
            continue
        if divisor_count(f)<=MAX_DIV:
            return dict(sorted(f.items()))
    chosen=list(pool[: min(5,len(pool))])
    f={2:vmin2,**{p:emin for p in chosen}}
    k=math.prod(p**e for p,e in f.items())
    if force_mod12 is not None and k%12!=force_mod12:
        f[5]=f.get(5,0)+1
    return dict(sorted(f.items()))

def certificate(q,f):
    assert math.prod(p**e for p,e in f.items())==q-1
    w={}
    for p in f:
        for a in range(2,502):
            if modpow(a,q-1,q)==1 and math.gcd(modpow(a,(q-1)//p,q)-1,q)==1:
                w[str(p)]=a;break
        else:return None
    return {'n':str(q),'factors':{str(p):e for p,e in f.items()},'witnesses':w}

def append(path,row):
    with path.open('a') as f:f.write(json.dumps(row)+'\n');f.flush()

def summarize(path):
    rows=[json.loads(s) for s in path.read_text().splitlines()] if path.exists() else []
    counts={}
    for r in rows:counts[r['status']]=counts.get(r['status'],0)+1
    return {'attempts_logged':len(rows),'status_counts':counts,
            'generation_seconds':round(sum(r.get('generation_seconds',0) for r in rows),3),
            'test_seconds':round(sum(r.get('test_seconds',0) for r in rows),3)}

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--seconds',type=float,default=300)
    ap.add_argument('--attempts',type=int,default=10000,help='additional attempts this run')
    ap.add_argument('--min-digits',type=int,default=100)
    ap.add_argument('--max-digits',type=int,default=300)
    ap.add_argument('--seed',type=int,default=20260922)
    ap.add_argument('--pool-max',type=int,default=31,help='odd primes in 5..pool-max')
    ap.add_argument('--nmin',type=int,default=5,help='odd primes multiplied into k')
    ap.add_argument('--nmax',type=int,default=7)
    ap.add_argument('--emin',type=int,default=1,help='min exponent of those odd primes')
    ap.add_argument('--emax',type=int,default=2)
    ap.add_argument('--no-cert',action='store_true',
                    help='log gmpy2 PRP hits as probable; prove later with cert.py')
    ap.add_argument('--hits-only',action='store_true',
                    help='do not write attempts.jsonl; keep hits, summary, and a small seen-k skip list')
    ap.add_argument('--family',choices=('tight','wide'),default='tight',
                    help='tight: k≡2 (mod 12). wide: even k, 3 does not divide k (2,4,8,10 mod 12)')
    ap.add_argument('--vmin2',type=int,default=None,help='override 2-adic valuation min')
    ap.add_argument('--vmax2',type=int,default=None,help='override 2-adic valuation max')
    ap.add_argument('--out',type=Path,default=Path('results'))
    args=ap.parse_args()
    if args.family=='tight':
        vmin2,vmax2,force_mod12=1,1,2
    else:
        vmin2,vmax2,force_mod12=1,3,None
    if args.vmin2 is not None:vmin2=max(1,args.vmin2)
    if args.vmax2 is not None:vmax2=max(vmin2,args.vmax2)
    if not (1<=args.min_digits<=args.max_digits<=250000 and args.seconds>0 and args.attempts>0):
        ap.error('Require positive time/attempts and 1 <= min-digits <= max-digits <= 250000')
    if args.pool_max<5 or args.nmin<1 or args.nmax<args.nmin or args.emin<1 or args.emax<args.emin:
        ap.error('Need pool-max>=5, 1<=nmin<=nmax, 1<=emin<=emax')
    args.out.mkdir(parents=True,exist_ok=True)
    pool=odd_primes_upto(args.pool_max)
    config={'version':7,'seed':args.seed,'min_digits':args.min_digits,'max_digits':args.max_digits,
            'pool_max':args.pool_max,'nmin':args.nmin,'nmax':args.nmax,
            'emin':args.emin,'emax':args.emax,'family':args.family,
            'vmin2':vmin2,'vmax2':vmax2,
            'no_cert':args.no_cert,'hits_only':args.hits_only}
    cp=args.out/'config.json'
    def norm(c):
        c=dict(c)
        c.setdefault('no_cert',False); c.setdefault('hits_only',False)
        c.setdefault('emin',1); c.setdefault('emax',2)
        c.setdefault('family','tight')
        c.setdefault('vmin2',1); c.setdefault('vmax2',1 if c.get('family')=='tight' else 3)
        c.pop('version',None)
        return c
    if cp.exists() and norm(json.loads(cp.read_text()))!=norm(config):
        ap.error('Config differs; choose a new --out folder')
    cp.write_text(json.dumps(config,indent=2))
    log=args.out/'attempts.jsonl';hits=args.out/'hits.jsonl'
    seen_k=args.out/'seen-k.txt';prog=args.out/'progress.json'
    if args.hits_only:
        prior_hits=[json.loads(s) for s in hits.read_text().splitlines()] if hits.exists() else []
        seen={r['candidate'] for r in prior_hits if 'candidate' in r}
        done=set(seen_k.read_text().splitlines()) if seen_k.exists() else {r['index'] for r in prior_hits if 'index' in r}
        start_id=json.loads(prog.read_text()).get('next_attempt',0) if prog.exists() else 0
        counts=json.loads(prog.read_text()).get('status_counts',{}) if prog.exists() else {}
        gen_s=json.loads(prog.read_text()).get('generation_seconds',0) if prog.exists() else 0
        test_s=json.loads(prog.read_text()).get('test_seconds',0) if prog.exists() else 0
    else:
        if log.exists():
            raw=log.read_bytes()
            if raw and not raw.endswith(b'\n'):log.write_bytes(raw[:raw.rfind(b'\n')+1])
        prior=[json.loads(s) for s in log.read_text().splitlines()] if log.exists() else []
        hits.write_text(''.join(json.dumps(r)+'\n' for r in prior if r['status'] in ('certified','probable')))
        seen={r['candidate'] for r in prior if 'candidate' in r}
        done={r['index'] for r in prior if 'index' in r}
        start_id=max((r['attempt'] for r in prior),default=-1)+1
        counts={}; gen_s=0; test_s=0
    small=[p for p in range(5,10000) if prime64(p)]
    started=time.monotonic();last=started;last_i=start_id-1
    print('engine',ENGINE,'Resume at attempt',start_id,'; output:',args.out,flush=True)
    try:
        for i in range(start_id,start_id+args.attempts):
            if time.monotonic()-started>=args.seconds:break
            f=index_for(i,args.seed,pool,args.nmin,args.nmax,args.emin,args.emax,
                        vmin2,vmax2,force_mod12)
            k=math.prod(p**e for p,e in f.items())
            row={'attempt':i,'index':str(k),'index_factors':f,'k_mod12':k%12}
            if str(k) in done:row['status']='duplicate-index'
            else:
                t=time.monotonic()
                try:
                    k,d,df=denominator(f)
                except ValueError:
                    row['status']='too-many-divisors'
                    counts[row['status']]=counts.get(row['status'],0)+1
                    done.add(str(k))
                    if args.hits_only:seen_k.open('a').write(str(k)+'\n')
                    else:append(log,row)
                    continue
                row['generation_seconds']=time.monotonic()-t
                gen_s+=row['generation_seconds']
                q=d+(1 if d%3==1 else -1)
                digits=int(q.bit_length()*math.log10(2))+1
                row.update(digits=digits,side='plus' if q==d+1 else 'minus')
                if not args.min_digits<=digits<=args.max_digits:
                    row['status']='outside-digit-band'
                else:
                    row['candidate']=str(q)
                    if row['candidate'] in seen:row['status']='duplicate-candidate'
                    elif q!=d+1:row['status']='minus-side-deferred'
                    else:
                        t=time.monotonic()
                        divisor=next((p for p in small if q!=p and q%p==0),None)
                        if divisor:row.update(status='sieved-composite',small_factor=divisor)
                        elif not is_prime(q):row['status']='mr-composite'
                        else:
                            row.update(door=str(d),denominator=str(3*d),door_factors=df)
                            if args.no_cert:
                                row['status']='probable'
                            else:
                                cert=certificate(q,df)
                                row['status']='certified' if cert else 'probable'
                                if cert:row['certificate']=cert
                        row['test_seconds']=time.monotonic()-t
                        test_s+=row['test_seconds']
            counts[row['status']]=counts.get(row['status'],0)+1
            fresh=str(k) not in done
            done.add(str(k))
            if args.hits_only:
                if fresh:seen_k.open('a').write(str(k)+'\n')
            else:append(log,row)
            if row.get('candidate'):seen.add(row['candidate'])
            if row['status'] in ('certified','probable'):
                append(hits,row)
                print('HIT',row['status'],row['digits'],'digits; zeta input',1-k,flush=True)
            if time.monotonic()-last>5:
                print('attempt',i+1,'elapsed',round(time.monotonic()-started,1),'s',flush=True);last=time.monotonic()
            last_i=i
    except KeyboardInterrupt:print('\nStopped; completed attempts saved.',flush=True)
    if args.hits_only:
        report={'attempts_logged':sum(counts.values()),'status_counts':counts,
                'generation_seconds':round(gen_s,3),'test_seconds':round(test_s,3)}
        prog.write_text(json.dumps({'next_attempt':last_i+1,'status_counts':counts,
                                    'generation_seconds':gen_s,'test_seconds':test_s},indent=2))
    else:
        report=summarize(log)
    (args.out/'summary.json').write_text(json.dumps(report,indent=2))
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()
