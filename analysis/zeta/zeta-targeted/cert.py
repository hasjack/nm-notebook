#!/usr/bin/env python3
"""Prove zeta-door hits. Default: only the longest candidate in the file.

    python3 cert.py kitchen-prp/hits.jsonl
    python3 cert.py --all kitchen-prp/hits.jsonl
"""
import argparse, json, sys, time
from pathlib import Path
import hunt

def prove(row):
    if row.get('status')=='certified' and row.get('certificate'):
        return row
    q=int(row['candidate'])
    df={int(p):e for p,e in row['door_factors'].items()}
    t=time.monotonic()
    cert=hunt.certificate(q,df)
    row['cert_seconds']=round(time.monotonic()-t,3)
    if not cert:
        row['status']='probable'
        return row
    row['status']='certified'
    row['certificate']=cert
    return row

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('src',type=Path)
    ap.add_argument('dst',type=Path,nargs='?')
    ap.add_argument('--all',action='store_true',help='prove every hit, not only the longest')
    args=ap.parse_args()
    rows=[json.loads(l) for l in args.src.read_text().splitlines() if l.strip()]
    if not rows:
        sys.exit('no hits')
    if not args.all:
        best=max(r.get('digits') or 0 for r in rows)
        rows=[r for r in rows if (r.get('digits') or 0)==best]
        if len(rows)>1:
            rows=[rows[0]]
    dst=args.dst or args.src.with_name(args.src.stem+'.certified.jsonl')
    n=0
    with dst.open('w') as out:
        for row in rows:
            row=prove(row)
            out.write(json.dumps(row)+'\n')
            print(row['status'], row.get('digits'), 'digits; zeta input', 1-int(row['index']), flush=True)
            n+=1
    print('Wrote', n, 'rows to', dst)

if __name__=='__main__':
    main()
