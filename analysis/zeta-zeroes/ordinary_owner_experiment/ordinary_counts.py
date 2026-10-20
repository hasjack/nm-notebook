"""Translate the mod-15 zero reconstruction to ordinary owner counts.
Uses cached numerical roots from full_test_results.json; no rerun of root scans.
The reconstruction is anchored to the exact count at x=100, explicitly.
Prime-power corrections are exact; character frequencies/amplitudes are fixed.
"""
from pathlib import Path
import json
import numpy as np
import mpmath as mp
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from scipy.integrate import cumulative_trapezoid
from scipy.special import expi

OUT=Path(__file__).parent
LIMIT=1_000_000
START=100
mp.mp.dps=25
cache=json.loads((OUT/'full_test_results.json').read_text())
flags=np.ones(LIMIT+1,dtype=bool);flags[:2]=False
for p in range(2,int(LIMIT**.5)+1):
    if flags[p]:flags[p*p::p]=False
primes=np.flatnonzero(flags)
owner_primes=primes[np.isin(primes%15,[4,11])]
records=[]
for p in primes:
    power=int(p);j=1
    while power<=LIMIT:
        if power%15 in [4,11]:records.append((power,int(p),j))
        power*=int(p);j+=1
records.sort()
powers=np.array([a for a,p,j in records])
logp=np.array([np.log(p) for a,p,j in records])
weights=np.array([1/j for a,p,j in records])
high=np.array([1/j if j>=2 else 0 for a,p,j in records])
all_idx=np.arange(len(records))
Jcum=np.cumsum(weights);Hcum=np.cumsum(high);Pcum=np.cumsum(logp)
def cumulative_at(t,positions,cumulative):
    inds=np.searchsorted(positions,t,side='right')-1
    return np.where(inds>=0,cumulative[np.maximum(inds,0)],0)
testx=np.array([100,1000,10000,100000,1000000])
direct=np.searchsorted(owner_primes,testx,side='right')
Jexact=cumulative_at(testx,powers,Jcum)
Hexact=cumulative_at(testx,powers,Hcum)
assert np.max(np.abs(Jexact-Hexact-direct))<1e-8
# Verify partial summation using the exact step-function integral.
# On [a,b), psi is constant and integral dt/(t log(t)^2)=1/log(a)-1/log(b).
def exact_partial_summation(t):
    sel=powers<=t
    pos=powers[sel];cum=Pcum[sel]
    if len(pos)==0:return 0.
    endpoints=np.r_[pos[1:],float(t)]
    integ=np.sum(cum*(1/np.log(pos)-1/np.log(endpoints)))
    return cum[-1]/np.log(t)+integ
assert max(abs(exact_partial_summation(t)-j) for t,j in zip(testx,Jexact))<1e-8

chi5=[0,1,-1,-1,1]
js={1:0,2:1,4:2,3:3}
chi15=[0 if a%3==0 or a%5==0 else (1 if a%3==1 else -1)*(1j**js[a%5]) for a in range(15)]
def even_constant(chi):
    first=mp.diff(lambda s:mp.dirichlet(s,chi),0)
    second=mp.diff(lambda s:mp.dirichlet(s,chi),0,2)
    return complex(second/(2*first))
b5,b15=even_constant(chi5),even_constant(chi15)
z5=[complex(.5,t) for t in cache['conductor5']['heights']]
z15=[complex(.5,t) for t in cache['conductor15']['heights']]
zz=[complex(mp.zetazero(i)) for i in range(1,41)]
zz=zz+[z.conjugate() for z in zz]

def calculate(points):
    t=np.geomspace(START,LIMIT,points)
    logt=np.log(t)
    correction=cumulative_at(t,powers,Hcum)
    C=np.searchsorted(owner_primes,t,side='right')
    C0=int(C[0]);H0=correction[0]
    # Log-derivative Euler-factor corrections for primes 3 and 5.
    principal_euler=np.zeros_like(t)
    induced_euler=np.zeros_like(t)
    for p in [3,5]:
        power=p;j=1
        while power<=LIMIT:
            principal_euler+=np.log(p)*(t>=power)
            if p==3:induced_euler+=np.log(3)*((-1)**j)*(t>=power)
            power*=p;j+=1
    basez=-np.log(2*np.pi)-.5*np.log1p(-t**-2)-principal_euler
    base5=-b5-logt-.5*np.log1p(-t**-2)-induced_euler
    base15=-b15-logt-.5*np.log1p(-t**-2)
    def psi(base,zeros,cut):
        out=base.astype(complex).copy()
        for rho in zeros:
            if abs(rho.imag)<=cut:out-=np.exp(rho*logt)/rho
        return out.real
    reference=C0+(expi(logt)-expi(np.log(START)))/4
    predictions={};metrics={}
    for cut in [20,40,80]:
        estimate=.25*(t+psi(basez,zz,cut))+.25*psi(base5,z5,cut)-.5*psi(base15,z15,cut)
        integral=cumulative_trapezoid(estimate/logt**2,logt,initial=0)
        Jdelta=estimate/logt-estimate[0]/logt[0]+integral
        pred=C0+Jdelta-(correction-H0)
        predictions[cut]=pred
        mask=t>=1000
        residual=C-reference
        metrics[cut]={'rms_count_error':float(np.sqrt(np.mean((pred[mask]-C[mask])**2))),
            'rms_error_relative_to_residual':float(np.sqrt(np.mean((pred[mask]-C[mask])**2))/np.sqrt(np.mean(residual[mask]**2))),
            'endpoint_predicted':float(pred[-1]),'endpoint_actual':int(C[-1])}
    return t,C,reference,predictions,metrics
t,C,reference,pred,metrics=calculate(65537)
t2,C2,reference2,pred2,metrics2=calculate(131073)
# Check integration resolution on matching nodes, rather than trusting a smooth overlay.
grid_check=float(np.sqrt(np.mean((pred[80]-pred2[80][::2])**2)))
assert grid_check<.05,grid_check
fig,ax=plt.subplots(2,1,figsize=(11,8),sharex=True,layout='constrained')
stride=32
for a,series,shift,title in [(ax[0],C2,0,'Ordinary owner count: classes 4 and 11 modulo 15'),(ax[1],C2-reference2,reference2,'Fluctuations around the anchored Li(x)/4 baseline')]:
    a.plot(np.log(t2[::stride]),series[::stride],color='#202020',lw=1.8,label='Direct prime-owner count')
    a.plot(np.log(t2[::stride]),(pred2[20]-shift)[::stride],color='#cf8b4e',lw=1,label='Zero-height cutoff 20')
    a.plot(np.log(t2[::stride]),(pred2[80]-shift)[::stride],color='#2776b6',ls='--',lw=1.1,label='Zero-height cutoff 80')
    a.set_title(title);a.grid(alpha=.18);a.legend(fontsize=9)
    a.set_ylabel('Owners' if a==ax[0] else 'Count minus baseline')
ax[1].set_xlabel('log x (100 to 1,000,000)')
fig.suptitle('From L-function zeros to ordinary Hire owner counts',fontsize=14)
fig.savefig(OUT/'mod15_ordinary_owner_counts.png',dpi=170,bbox_inches='tight',pad_inches=.2)
report={'exact_checks':[{'x':int(x),'ordinary_count':int(c),'prime_power_weighted_count':float(j),'higher_power_correction':float(h)} for x,c,j,h in zip(testx,direct,Jexact,Hexact)],
    'metrics':metrics2,'integration_grid_rms_difference':grid_check,
    'anchor':{'x':START,'exact_owner_count':int(np.searchsorted(owner_primes,START,side='right'))},
    'method':'Partial summation of truncated unsmoothed explicit formula, exact higher-prime-power corrections, exact initial-count anchor at 100. Frequencies and coefficients fixed. Cached critical-line roots are numerical and uncertified.'}
(OUT/'ordinary_counts_results.json').write_text(json.dumps(report,indent=2))
print(json.dumps(report,indent=2))
