"""Independent trial-division check of the census through 10,000."""
from pathlib import Path
from math import isqrt
import tempfile,subprocess,sys,shutil,json

def trial(n):
    s=set();r=2
    while r*r<=n:
        while n%r==0:s.add(r);n//=r
        r+=1
    if n>1:s.add(n)
    return s

def odddoor(p):return trial(p+(1 if p%3==1 else -1))-{2}
primes=[n for n in range(5,10001,2) if all(n%r for r in range(2,isqrt(n)+1))]
disjoint=linked=non5=0
for a,b in zip(primes,primes[1:]):
    old,new=odddoor(a),odddoor(b)
    if old&new:continue
    disjoint+=1
    matches={q for q in old if any((r+(1 if r%3==1 else -1))%q==0 for r in new)}
    linked+=bool(matches);non5+=bool(matches-{5})
here=Path(__file__).resolve().parent
with tempfile.TemporaryDirectory() as temp:
    for name in ['deeper_connections.py','waits.py','ingredient_transitions.py']:shutil.copy(here/name,Path(temp)/name)
    subprocess.run([sys.executable,str(Path(temp)/'deeper_connections.py'),'--limit','10000'],check=True,stdout=subprocess.DEVNULL)
    c=json.loads((Path(temp)/'deeper-connections.json').read_text())['counts']
    assert c['pairs']==len(primes)-1
    assert c['disjoint']==disjoint and c['disjoint_with_deeper']==linked
    assert c['disjoint_with_deeper_other_than_5']==non5
print(f'Independent check passed: {disjoint} disjoint transitions; {linked} deeper connections; {non5} via non-5 factors.')
