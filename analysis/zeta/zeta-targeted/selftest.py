"""Small mathematical regression checks; python3 selftest.py."""
from fractions import Fraction as F
from math import comb
import copy,json,tempfile,subprocess,sys
from pathlib import Path
import hunt,verify

B=[F(1)]
for m in range(1,202):B.append(-sum((comb(m+1,j)*B[j] for j in range(m)),F(0))/(m+1))
def factor(n):
    out={};p=2
    while p*p<=n:
        while n%p==0:out[p]=out.get(p,0)+1;n//=p
        p+=1
    if n>1:out[n]=1
    return out
for k in range(2,202):
    if k%2 or k%3==0:continue
    _,d,_=hunt.denominator(factor(k))
    assert 3*d==(B[k]/k).denominator
# ChatGPT's four examples: neighbours 5, 41, 79, 43.
assert hunt.denominator(factor(2))[1]==4
assert hunt.denominator(factor(4))[1]==40
assert hunt.denominator(factor(8))[1]==80
assert hunt.denominator(factor(10))[1]==44
for n in range(2,10000):
    expected=all(n%p for p in range(2,__import__('math').isqrt(n)+1))
    assert hunt.prime64(n)==verify.isprime64(n)==expected
assert not verify.isprime64(2**64)
assert not verify.isprime64(24793667968257483011)  # 20-digit; not a 64-bit proof
row=json.loads(Path('pilot/hits.jsonl').read_text().splitlines()[0])
verify.validate(row)
bad=copy.deepcopy(row);bad['certificate']['witnesses']['2']=1
try:verify.validate(bad)
except AssertionError:pass
else:raise AssertionError('Bad certificate accepted')
bad=copy.deepcopy(row);bad['denominator']=str(int(bad['denominator'])+6)
try:verify.validate(bad)
except AssertionError:pass
else:raise AssertionError('Bad denominator accepted')
with tempfile.TemporaryDirectory() as tmp:
    cmd=[sys.executable,'hunt.py','--attempts','10','--seconds','30','--out',tmp]
    subprocess.run(cmd,check=True,stdout=subprocess.DEVNULL)
    subprocess.run(cmd,check=True,stdout=subprocess.DEVNULL)
    rows=[json.loads(s) for s in (Path(tmp)/'attempts.jsonl').read_text().splitlines()]
    assert [r['attempt'] for r in rows]==list(range(20))
print('PASS: exact small denominators, primality kernels, corrupted certificate rejection, resume')
