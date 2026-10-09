"""Exploratory Hardy-Littlewood-style local model, not a proven asymptotic.
Every multiplier is enumerated before seeing observations, including zero-hit cases.
Weighted model S(A) integral_5^Y dr/log(r); log(p) cancels in pair intensity.
"""
import math,json,csv,argparse
from pathlib import Path
import numpy as np
import mpmath as mp
import matplotlib.pyplot as plt

def multipliers(limit):
 out=[];two=2
 while two*5<=limit:
  five=5
  while two*five<=limit:
   three=1;b=0
   while two*five*three<=limit:
    out.append((two*five*three,b));three*=3;b+=1
   five*=5
  two*=2
 return sorted(out)

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--max',type=int,default=10000000);ap.add_argument('--out',default='.');args=ap.parse_args();N=args.max;out=Path(args.out);out.mkdir(parents=True,exist_ok=True)
 sieve=np.ones(N+2,dtype=bool);sieve[:2]=False
 for q in range(2,math.isqrt(N+1)+1):
  if sieve[q]:sieve[q*q::q]=False
 p=np.flatnonzero(sieve);p=p[(p>3)&(p<=N)];chi=np.where(p%3==1,1,-1);m0=p+chi;m1=p-chi;a=(m0%5==0).astype(int)-(m1%5==0).astype(int);active=a!=0;p=p[active];chi=chi[active];a=a[active];d=np.where(a==1,p+chi,p-chi);r=d.copy()
 for q in [2,3,5]:
  mask=r%q==0
  while mask.any():r[mask]//=q;mask=r%q==0
 one=sieve[r]&(r>5);p=p[one];a=a[one];d=d[one];r=r[one];A=d//r;eps=p-d
 assert np.all(np.abs(eps)==1);assert np.all((A%3==0)==(a==-1))
 # Independent expected one-factor bin check at 10^7.
 if N==10000000:assert len(p)==112285
 small=np.flatnonzero(sieve[:100001]);small=small[small>2]
 twoC=2*float(np.prod(1-1/(small.astype(float)-1)**2))
 base=twoC*(4/3) # A divisible by5; factor2 already accounted for
 allA=multipliers(N//7+1);checkpoints=[x for x in [1000000,3000000,10000000] if x<=N];summary=[];caseRows=[]
 for X in checkpoints:
  mask=p<=X;obs={}
  keys=np.stack([A[mask],eps[mask]],axis=1);uniq,inv=np.unique(keys,axis=0,return_inverse=True);weights=np.bincount(inv,weights=np.log(p[mask]));counts=np.bincount(inv)
  obs={(int(k[0]),int(k[1])):(int(n),float(w)) for k,n,w in zip(uniq,counts,weights)}
  cases=[]
  for mult,b in allA:
   sign=1 if b==0 else -1;S=base if b==0 else 2*base
   for e in [-1,1]:
    Y=(X-e)//mult
    if Y<7:continue
    count,w=obs.get((mult,e),(0,0.));pred=S*float(mp.ei(mp.log(Y))-mp.ei(mp.log(5)))
    cases.append({'X':X,'A':mult,'epsilon':e,'v3_A':b,'sign':sign,'r_upper':Y,'observed_count':count,'observed_weight':w,'predicted_weight':pred,'singular_series':S})
  caseRows+=cases
  for cut in [100,1000,10000]:
   good=[c for c in cases if c['r_upper']>=cut];plus=sum(c['observed_weight'] for c in good if c['sign']==1);minus=sum(c['observed_weight'] for c in good if c['sign']==-1);predplus=sum(c['predicted_weight'] for c in good if c['sign']==1);predminus=sum(c['predicted_weight'] for c in good if c['sign']==-1)
   summary.append({'X':X,'minimum_r_upper':cut,'observed_plus':plus,'observed_minus':minus,'observed_signed':plus-minus,'predicted_plus':predplus,'predicted_minus':predminus,'predicted_signed':predplus-predminus,'omitted_signed':float(np.sum(a[mask]*np.log(p[mask])))-(plus-minus),'observed_over_predicted_plus':plus/predplus,'observed_over_predicted_minus':minus/predminus})
 result={'max':N,'finite_product_prime_cutoff':100000,'base_singular_series':base,'summary':summary,'all_one_factor_signed':float(np.sum(a*np.log(p))),'definition':'Selected door d=A*r with r prime>5 and A=2^a3^b5^c, a,c>=1; kept b=0, discarded b>=1; owner p=A*r+epsilon. Predicted weight S(A)*(Ei(log Y)-Ei(log5)), Y=floor((X-epsilon)/A).','warning':'Heuristic two-prime intensity. Multipliers with short cofactor ranges are excluded by the displayed thresholds. No cancellation bound or asymptotic is proved.'}
 (out/'cofactor_model.json').write_text(json.dumps(result,indent=2))
 with (out/'multiplier_cases.csv').open('w') as f:wr=csv.DictWriter(f,fieldnames=caseRows[0].keys());wr.writeheader();wr.writerows(caseRows)
 fig,axes=plt.subplots(1,2,figsize=(12,5));rr=[c for c in summary if c['minimum_r_upper']==1000];xx=np.arange(len(rr));axes[0].bar(xx-.18,[c['observed_signed'] for c in rr],width=.36,label='Observed');axes[0].bar(xx+.18,[c['predicted_signed'] for c in rr],width=.36,label='Local pair heuristic');axes[0].set_xticks(xx,[f"{c['X']/1e6:g}m" for c in rr]);axes[0].set(title='One-factor signed bias: long cofactor ranges',xlabel='Prime cutoff X',ylabel='Signed logarithmic weight');axes[0].legend()
 rr=[c for c in summary if c['X']==N];xx=np.arange(len(rr));axes[1].bar(xx-.18,[c['observed_over_predicted_plus'] for c in rr],width=.36,label='Kept (+)');axes[1].bar(xx+.18,[c['observed_over_predicted_minus'] for c in rr],width=.36,label='Discarded (−)');axes[1].set_xticks(xx,[str(c['minimum_r_upper']) for c in rr]);axes[1].axhline(1,color='#555',ls='--');axes[1].set(title='Separate sides: observed / heuristic',xlabel='Minimum upper endpoint of cofactor range',ylabel='Ratio');axes[1].legend();
 for ax in axes:ax.grid(alpha=.2)
 fig.suptitle('Exact multiplier cases explain most of the one-factor bias',fontsize=15);fig.text(.5,.015,'Heuristic local densities for two simultaneous primes. Agreement is an empirical check, not a proved bound.',ha='center',fontsize=9);fig.tight_layout(rect=(0,.04,1,.93));fig.savefig(out/'cofactor_model.png',dpi=160)
 print(json.dumps(result,indent=2))
if __name__=='__main__':main()
