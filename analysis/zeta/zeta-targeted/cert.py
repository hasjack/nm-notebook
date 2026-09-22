#!/usr/bin/env python3
"""Prove probable zeta-door hits. python3 cert.py kitchen8/hits.jsonl"""
import json, sys
from pathlib import Path
import hunt

def prove(row):
    if row.get('status')=='certified' and row.get('certificate'):
        return row
    q=int(row['candidate'])
    df={int(p):e for p,e in row['door_factors'].items()}
    cert=hunt.certificate(q,df)
    if not cert:
        row['status']='probable'
        return row
    row['status']='certified'
    row['certificate']=cert
    return row

def main():
    src=Path(sys.argv[1])
    dst=Path(sys.argv[2]) if len(sys.argv)>2 else src.with_name(src.stem+'.certified.jsonl')
    n=0
    with dst.open('w') as out:
        for line in src.read_text().splitlines():
            if not line.strip():continue
            row=prove(json.loads(line))
            out.write(json.dumps(row)+'\n')
            print(row['status'], row.get('digits'), 'digits; zeta input', 1-int(row['index']), flush=True)
            n+=1
    print('Wrote', n, 'rows to', dst)

if __name__=='__main__':
    main()
