#!/usr/bin/env python3
"""Target exact zeta denominators; standard-library Python 3.9+.
python3 hunt.py --seconds 300 --attempts 10000
python3 verify.py results/hits.jsonl
"""
import argparse, json, math, random, time
from pathlib import Path
from functools import lru_cache

BASES64=(2,325,9375,28178,450775,9780504,1795265022)
BASES=(2,3,5,7,11,13,17,19,23,29,31,37)
POOL=(5,7,11,13,17,19,23,29,31)

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

def denominator(f):
    k=math.prod(p**e for p,e in f.items())
    if k>=2**64-1:raise ValueError('Index too large for exact factor certification')
    assert k%12==2
    factors={}
    for d in divisors(f):
        p=d+1
        if prime64(p):
            e=1;t=k
            while t%p==0:t//=p;e+=1
            factors[p]=e
    assert factors.pop(3)==1
    return k,math.prod(p**e for p,e in factors.items()),factors

def index_for(i,seed):
    rng=random.Random(seed+i)
    chosen=rng.sample(POOL,rng.randint(5,7))
    f={2:1,**{p:rng.randint(1,2) for p in chosen}}
    k=math.prod(p**e for p,e in f.items())
    if k%12!=2:f[5]=f.get(5,0)+1
    return dict(sorted(f.items()))

def certificate(q,f):
    assert math.prod(p**e for p,e in f.items())==q-1
    w={}
    for p in f:
        for a in range(2,258):
            if pow(a,q-1,q)==1 and math.gcd(pow(a,(q-1)//p,q)-1,q)==1:
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
    ap.add_argument('--out',type=Path,default=Path('results'))
    args=ap.parse_args()
    if not (1<=args.min_digits<=args.max_digits<=4000 and args.seconds>0 and args.attempts>0):
        ap.error('Require positive time/attempts and 1 <= min-digits <= max-digits <= 4000')
    args.out.mkdir(parents=True,exist_ok=True)
    config={'version':1,'seed':args.seed,'min_digits':args.min_digits,'max_digits':args.max_digits}
    cp=args.out/'config.json'
    if cp.exists() and json.loads(cp.read_text())!=config:ap.error('Config differs; choose a new --out folder')
    cp.write_text(json.dumps(config,indent=2))
    log=args.out/'attempts.jsonl';hits=args.out/'hits.jsonl'
    # A crash may leave a partial final line; discard only that unfinished record.
    if log.exists():
        raw=log.read_bytes()
        if raw and not raw.endswith(b'\n'):log.write_bytes(raw[:raw.rfind(b'\n')+1])
    prior=[json.loads(s) for s in log.read_text().splitlines()] if log.exists() else []
    # Derive hit file from the authoritative attempt log, recovering interrupted writes.
    hits.write_text(''.join(json.dumps(r)+'\n' for r in prior if r['status'] in ('certified','probable')))
    seen={r['candidate'] for r in prior if 'candidate' in r}
    done={r['index'] for r in prior if 'index' in r}
    start_id=max((r['attempt'] for r in prior),default=-1)+1
    small=[p for p in range(5,10000) if prime64(p)]
    started=time.monotonic();last=started
    print('Resume at attempt',start_id,'; output:',args.out,flush=True)
    try:
        for i in range(start_id,start_id+args.attempts):
            if time.monotonic()-started>=args.seconds:break
            f=index_for(i,args.seed);k=math.prod(p**e for p,e in f.items())
            row={'attempt':i,'index':str(k),'index_factors':f}
            if str(k) in done:row['status']='duplicate-index'
            elif k>=2**64-1:row['status']='index-limit'
            else:
                t=time.monotonic();k,d,df=denominator(f)
                row['generation_seconds']=time.monotonic()-t
                q=d+(1 if d%3==1 else -1);digits=len(str(q))
                row.update(candidate=str(q),digits=digits,side='plus' if q==d+1 else 'minus')
                if str(q) in seen:row['status']='duplicate-candidate'
                elif not args.min_digits<=digits<=args.max_digits:row['status']='outside-digit-band'
                elif q!=d+1:row['status']='minus-side-deferred'
                else:
                    t=time.monotonic()
                    divisor=next((p for p in small if q!=p and q%p==0),None)
                    if divisor:row.update(status='sieved-composite',small_factor=divisor)
                    elif not mr(q,BASES):row['status']='mr-composite'
                    else:
                        cert=certificate(q,df)
                        row.update(status='certified' if cert else 'probable',door=str(d),
                                   denominator=str(3*d),door_factors=df)
                        if cert:row['certificate']=cert
                    row['test_seconds']=time.monotonic()-t
            append(log,row);done.add(str(k))
            if 'candidate' in row:seen.add(row['candidate'])
            if row['status'] in ('certified','probable'):
                append(hits,row)
                print('HIT',row['status'],row['digits'],'digits; zeta input',1-k,flush=True)
            if time.monotonic()-last>5:
                print('attempt',i+1,'elapsed',round(time.monotonic()-started,1),'s',flush=True);last=time.monotonic()
    except KeyboardInterrupt:print('\nStopped; completed attempts saved.',flush=True)
    report=summarize(log);(args.out/'summary.json').write_text(json.dumps(report,indent=2))
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()
