#!/usr/bin/env python3
"""Shard hunt.py across cores. PRP only. Merge hits when done.

    python3 hunt_mp.py --jobs 8 --no-cert --hits-only \\
      --min-digits 12000 --max-digits 25000 \\
      --pool-max 47 --nmin 9 --nmax 9 --emin 2 --emax 2 \\
      --attempts 20000 --seconds 14400 --out lions
"""
import argparse, json, os, subprocess, sys, time
from pathlib import Path

HERE=Path(__file__).resolve().parent
HUNT=HERE/'hunt.py'

def main():
    ap=argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--jobs',type=int,default=max(1,(os.cpu_count() or 2)-2),
                    help='worker processes (default: cpu_count-2)')
    args, rest=ap.parse_known_args()
    if args.jobs<1:ap.error('jobs>=1')
    # pull --out and --attempts/--seed from rest for sharding
    out=Path('lions'); attempts=20000; seed=20260928; seconds=14400
    stripped=[]
    it=iter(rest)
    for tok in it:
        if tok=='--out':out=Path(next(it))
        elif tok=='--attempts':attempts=int(next(it))
        elif tok=='--seed':seed=int(next(it))
        elif tok=='--seconds':seconds=float(next(it))
        else:stripped.append(tok)
    out.mkdir(parents=True,exist_ok=True)
    per=max(1,attempts//args.jobs)
    print(f'jobs {args.jobs}  attempts/job {per}  total ~{per*args.jobs}  out {out}',flush=True)
    procs=[]
    t0=time.time()
    for w in range(args.jobs):
        wout=out/f'w{w}'
        wout.mkdir(parents=True,exist_ok=True)
        cmd=[sys.executable,str(HUNT),'--out',str(wout),'--attempts',str(per),
             '--seed',str(seed+w*1_000_003),'--seconds',str(seconds),*stripped]
        log=open(out/f'w{w}.log','w')
        p=subprocess.Popen(cmd,cwd=str(HERE),stdout=log,stderr=subprocess.STDOUT)
        procs.append((w,p,log))
        print(f'  started w{w} pid {p.pid} seed {seed+w*1_000_003}',flush=True)
    rc=0
    try:
        while any(p.poll() is None for _,p,_ in procs):
            time.sleep(5)
            hits=0
            for w,_,_ in procs:
                hp=out/f'w{w}'/'hits.jsonl'
                if hp.exists():
                    hits+=sum(1 for line in hp.read_text().splitlines() if line.strip())
            print(f'\relapsed {time.time()-t0:.0f}s  hits {hits}  live {sum(p.poll() is None for _,p,_ in procs)}/{args.jobs}',end='',flush=True)
    except KeyboardInterrupt:
        print('\nstopping workers',flush=True)
        for _,p,_ in procs:p.terminate()
    print()
    for w,p,log in procs:
        p.wait(); log.close()
        if p.returncode not in (0,None,-15):rc=p.returncode or rc
        print(f'w{w} exit {p.returncode}')
    merged=out/'hits.jsonl'
    rows=[]
    for w,_,_ in procs:
        hp=out/f'w{w}'/'hits.jsonl'
        if hp.exists():
            for line in hp.read_text().splitlines():
                if line.strip():rows.append(json.loads(line))
    rows.sort(key=lambda r:(-(r.get('digits') or 0), r.get('index','')))
    merged.write_text(''.join(json.dumps(r)+'\n' for r in rows))
    print(f'merged {len(rows)} hits -> {merged}')
    if rows:
        top=rows[0]
        print('champion', top.get('digits'), 'digits; zeta input', 1-int(top['index']))
    print(f'wall {time.time()-t0:.1f}s')
    sys.exit(rc)

if __name__=='__main__':
    main()
