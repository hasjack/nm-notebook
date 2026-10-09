"""Reproducible exploratory door cancellation diagnostic; numpy/matplotlib.
Controls permute signs within dyadic size x mod-3 strata, preserving sign counts.
Graph is gold graph on odd primes !=3, with edges from kept-door factors.
"""
import argparse, json, csv, math
from pathlib import Path
from collections import defaultdict
import numpy as np
import matplotlib.pyplot as plt

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--max',type=int,default=3000000);ap.add_argument('--permutations',type=int,default=199);ap.add_argument('--out',default='.');args=ap.parse_args();out=Path(args.out);out.mkdir(parents=True,exist_ok=True)
 M=args.max;spf=np.zeros(M+2,dtype=np.int32)
 for p in range(2,M+2):
  if spf[p]==0:
   spf[p]=p
   if p*p<=M+1:
    v=spf[p*p::p];v[v==0]=p
 primes=np.flatnonzero(spf==np.arange(M+2));primes=primes[primes>=2];primes=primes[primes<=M]
 parent=np.arange(M+2,dtype=np.int32)
 def root(a):
  while parent[a]!=a:parent[a]=parent[parent[a]];a=int(parent[a])
  return a
 def union(a,b):
  a,b=root(a),root(b)
  if a!=b:
   parent[max(a,b)]=min(a,b);return 1
  return 0
 def factors(n):
  fs=[]
  while n>1:
   q=int(spf[n]);e=0
   while n%q==0:n//=q;e+=1
   fs.append((q,e))
  return fs
 def v(n,q):
  e=0
  while n%q==0:n//=q;e+=1
  return e
 def geometry(n):
  for q in (2,3,5):
   while n%q==0:n//=q
  fs=factors(n)
  return sum(e for q,e in fs),len(fs),max((q for q,e in fs),default=1),n
 rows=[];checkpoints=sorted(set(x for x in [10000,100000,1000000,M] if x<=M));summary=[];B=0.;absw=0.;idx=0
 for pp in primes:
  p=int(pp)
  while idx<len(checkpoints) and checkpoints[idx]<p:
   X=checkpoints[idx];mainroot=root(5);act=np.array(rows,dtype=float) if rows else np.empty((0,11));summary.append({'X':X,'active':len(rows),'B':B,'absolute_weight':absw,'B_over_sqrtX':B/math.sqrt(X),'satellite_active':sum(root(int(r[0]))!=mainroot for r in rows),'satellite_B':sum(r[1]*math.log(r[0]) for r in rows if root(int(r[0]))!=mainroot)});idx+=1
  if p in (2,3):continue
  chi=1 if p%3==1 else -1;m0=p+chi;m1=p-chi
  merges=0
  for q,e in factors(m0):
   if q>2:merges+=union(p,q)
  a=int(m0%5==0)-int(m1%5==0)
  assert a==({4:1,11:1,1:-1,14:-1}.get(p%15,0))
  if not a:continue
  selected=m0 if a==1 else m1
  om,distinct,lpf,co=geometry(selected)
  # integer fields: p, sign, selected v5, kept v2, discarded v2, stripped Omega, distinct, lpf log ratio, dyadic, mod3, cofactor
  both=[(q,e) for nn in (m0,m1) for q,e in factors(nn) if q not in (2,3,5)]
  common_omega=sum(e for q,e in both);common_lpf=max((q for q,e in both),default=1)
  rows.append([p,a,v(selected,5),v(m0,2),v(m1,2),om,distinct,math.log(lpf)/math.log(p),p.bit_length()-1,p%3,co,common_omega,math.log(common_lpf)/math.log(p),int(merges>=2)])
  B+=a*math.log(p);absw+=math.log(p)
 while idx<len(checkpoints):
  X=checkpoints[idx];mainroot=root(5);summary.append({'X':X,'active':len(rows),'B':B,'absolute_weight':absw,'B_over_sqrtX':B/math.sqrt(X),'satellite_active':sum(root(int(r[0]))!=mainroot for r in rows),'satellite_B':sum(r[1]*math.log(r[0]) for r in rows if root(int(r[0]))!=mainroot)});idx+=1
 R=np.array(rows,dtype=float);w=np.log(R[:,0]);sgn=R[:,1];strata=R[:,8].astype(int)*3+R[:,9].astype(int);groups=[np.flatnonzero(strata==k) for k in np.unique(strata)]
 features={'both_doors_Omega':np.minimum(R[:,11],10).astype(int),'both_doors_largest_ratio':np.minimum((R[:,12]*5).astype(int),4),'gold_merge_event':R[:,13].astype(int),'selected_v5':np.minimum(R[:,2],4).astype(int),'kept_v2':np.minimum(R[:,3],6).astype(int),'discarded_v2':np.minimum(R[:,4],6).astype(int),'stripped_Omega':np.minimum(R[:,5],6).astype(int),'stripped_distinct':np.minimum(R[:,6],5).astype(int),'largest_factor_log_ratio':np.minimum((R[:,7]*5).astype(int),4)}
 rng=np.random.default_rng(20261009);results={};categories=[]
 for name,bins in features.items():
  K=int(bins.max())+1;obs=np.bincount(bins,weights=w*sgn,minlength=K);mass=np.bincount(bins,weights=w,minlength=K);count=np.bincount(bins,minlength=K);sims=[]
  for _ in range(args.permutations):
   shuffled=sgn.copy()
   for ids in groups:shuffled[ids]=rng.permutation(sgn[ids])
   sims.append(np.bincount(bins,weights=w*shuffled,minlength=K))
  sims=np.array(sims);mean=sims.mean(0);sd=sims.std(0,ddof=1);z=np.divide(obs-mean,sd,out=np.zeros(K),where=sd>0)
  results[name]=[{'bin':int(j),'count':int(count[j]),'signed_weight':float(obs[j]),'absolute_weight':float(mass[j]),'null_mean':float(mean[j]),'null_sd':float(sd[j]),'z':float(z[j])} for j in range(K)];categories.extend((name,j,float(z[j])) for j in range(K) if count[j]>=100)
 # same predeclared feature partitions at earlier checkpoints, descriptive stability
 stability={}
 for X in checkpoints:
  ids=R[:,0]<=X;stability[str(X)]={name:[{'bin':int(j),'count':int(np.sum(ids&(bins==j))),'signed_weight':float(np.sum(w[ids&(bins==j)]*sgn[ids&(bins==j)]))} for j in np.unique(bins)] for name,bins in features.items()}
 data={'max':M,'seed':20261009,'permutations':args.permutations,'definition':'sum over odd primes p!=3 of log(p)*(1[5|m0(p)]-1[5|m1(p)])','checkpoints':summary,'feature_bins':results,'stability':stability,'interpretation':'Exploratory conditional dependence. Sign shuffling preserves sign counts by dyadic size and p mod3. These features can encode sign arithmetically; significant bins alone do not supply cancellation bounds.'}
 (out/'results.json').write_text(json.dumps(data,indent=2));
 with (out/'checkpoints.csv').open('w') as f:
  wr=csv.DictWriter(f,fieldnames=summary[0].keys());wr.writeheader();wr.writerows(summary)
 xs=R[:,0];cum=np.cumsum(w*sgn);fig,axes=plt.subplots(2,2,figsize=(13,9));ax=axes[0,0];ax.plot(xs,cum,label='B₅(X)',color='#335ca8');ax.plot(xs,np.sqrt(xs),ls='--',color='#aaa',label='±√X reference');ax.plot(xs,-np.sqrt(xs),ls='--',color='#aaa');ax.set_xscale('log');ax.set(title='Signed logarithmic prime sum',xlabel='X',ylabel='B₅(X)');ax.legend()
 ax=axes[0,1];name='selected_v5';rr=results[name];ax.bar([r['bin'] for r in rr],[r['signed_weight'] for r in rr],color='#335ca8',label='Observed');ax.errorbar([r['bin'] for r in rr],[r['null_mean'] for r in rr],yerr=[2*r['null_sd'] for r in rr],fmt='o',color='#e07b32',label='Conditional shuffle mean ±2 sd');ax.set(title='Multiplicity of hub 5 in the selected door',xlabel='v₅ (4 includes larger values)',ylabel='Signed log weight');ax.legend(fontsize=9)
 ax=axes[1,0];name='stripped_Omega';rr=results[name];ax.bar([r['bin'] for r in rr],[r['signed_weight'] for r in rr],color='#335ca8');ax.errorbar([r['bin'] for r in rr],[r['null_mean'] for r in rr],yerr=[2*r['null_sd'] for r in rr],fmt='o',color='#e07b32');ax.set(title='Door factors after removing 2, 3 and 5',xlabel='Number of remaining factors, with multiplicity (6+)',ylabel='Signed log weight')
 ax=axes[1,1];take=[(n,j,z) for n,j,z in categories if n in ('stripped_Omega','stripped_distinct','largest_factor_log_ratio')];ax.barh([n+' bin '+str(j) for n,j,z in take],[z for n,j,z in take],color=['#c65b36' if z>0 else '#335ca8' for n,j,z in take]);ax.axvline(0,color='#444');ax.set(title='Factor geometry strongly conditions the sign',xlabel='Deviation / shuffle standard deviation');ax.tick_params(axis='y',labelsize=8)
 for ax in axes.flat:ax.grid(alpha=.18)
 fig.suptitle(f'Door cancellation lab · primes through {M:,}',fontsize=18);fig.text(.5,.01,'Exploratory controls: sign counts preserved within size × mod-3 strata. Conditional effects are not new cancellation bounds.',ha='center',fontsize=10);fig.tight_layout(rect=(0,.035,1,.96));fig.savefig(out/'door_lab.png',dpi=160)
 print(json.dumps({'checkpoints':summary,'largest_conditional_deviations':sorted(categories,key=lambda r:abs(r[2]),reverse=True)[:12]},indent=2))
if __name__=='__main__':main()
