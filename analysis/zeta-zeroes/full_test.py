"""Numerical explicit-formula test for the full mod-15 observable.
Critical-line zeros are numerical roots, not a certified complete zero list.
Two nested scans and root residual checks are used. No fitted parameters.
"""
from pathlib import Path
import json, time, runpy
import numpy as np
import mpmath as mp
import matplotlib.pyplot as plt

OUT=Path(__file__).parent
d=runpy.run_path(str(OUT/'run.py'))
x,scale=d['x'],d['scale']
mp.mp.dps=25
chi5=[0,1,-1,-1,1]
js={1:0,2:1,4:2,3:3}
chi15=[0 if a%3==0 or a%5==0 else
       (1 if a%3==1 else -1)*(1j**js[a%5]) for a in range(15)]
for chi in [chi5,chi15]:
    f=len(chi)
    assert chi[-1]==1
    for a in range(f):
        for b in range(f): assert chi[(a*b)%f]==chi[a]*chi[b]

def L(s,chi): return mp.dirichlet(s,chi)

def scan_zeros(chi,T=80):
    f=len(chi)
    tau=sum(chi[a]*mp.exp(2j*mp.pi*a/f) for a in range(f))
    W=tau/mp.sqrt(f)
    assert abs(abs(W)-1)<mp.mpf('1e-20')
    phase=mp.exp(-.5j*mp.arg(W))
    max_imag=mp.mpf(0)
    def hardy(t):
        nonlocal max_imag
        s=mp.mpf('.5')+1j*t
        factor=mp.power(f/mp.pi,s/2)*mp.gamma(s/2)
        z=phase*factor*L(s,chi)/abs(factor)
        max_imag=max(max_imag,abs(z.imag))
        return z.real
    lo=0 if f==5 else -T
    grid=np.arange(lo,T+.0625,.125)
    vals=[hardy(mp.mpf(float(t))) for t in grid]
    counts={}
    brackets=[]
    for stride in [2,1]:
        found=[]
        for i in range(0,len(grid)-stride,stride):
            if vals[i]*vals[i+stride]<0: found.append((grid[i],grid[i+stride]))
        counts[str(.125*stride)]=len(found)
        if stride==1: brackets=found
    assert len(set(counts.values()))==1,counts
    roots=[]
    for a,b in brackets:
        t=mp.findroot(hardy,(mp.mpf(float(a)),mp.mpf(float(b))),solver='anderson',tol=mp.mpf('1e-21'))
        assert a<t<b
        if not roots or abs(t-roots[-1])>mp.mpf('1e-12'): roots.append(t)
    residual=max(abs(L(mp.mpf('.5')+1j*t,chi)) for t in roots)
    assert residual<mp.mpf('1e-17'),residual
    assert max_imag<mp.mpf('1e-18'),max_imag
    print('zeros',f,'counts',counts,'max_L_residual',float(residual),'heights',[float(t) for t in roots[:6]],flush=True)
    if f==5: roots=sorted([-t for t in roots]+roots)
    return [complex(.5,float(t)) for t in roots],{'counts':counts,'max_L_residual':float(residual),'max_hardy_imaginary':float(max_imag),'heights':[float(t) for t in roots]}

start=time.time()
z5,info5=scan_zeros(chi5)
z15,info15=scan_zeros(chi15)

def analytic_base(chi):
    # L(s)=L'(0)s + L''(0)s^2/2+... for these primitive even characters.
    # Residue at s=0 of -L'/L(s)*x^(s+1)/(s(s+1)) is x*(1-b-log x).
    first=mp.diff(lambda s:L(s,chi),0)
    second=mp.diff(lambda s:L(s,chi),0,2)
    b=complex(second/(2*first))
    constant=complex(mp.dirichlet(-1,chi,1)/L(-1,chi))
    base=x*(1-b-np.log(x))+constant
    for k in range(1,12): base-=x**(1-2*k)/(2*k*(2*k-1))
    return base
base5=analytic_base(chi5)
# The quadratic character modulo 15 is induced from conductor 5:
# remove the 3-power coefficients from its primitive prime-power sum.
power=3;j=1
while power<=d['LIMIT']:
    base5-=np.log(3)*((-1)**j)*np.maximum(x-power,0)
    power*=3;j+=1
base15=analytic_base(chi15)
def recon(base,zeros,T):
    ans=base.copy()
    for rho in zeros:
        if abs(rho.imag)<=T:
            ans-=np.exp((rho+1)*np.log(x))/(rho*(rho+1))
    return ans.real

baseline_other=(.25*base5.real-.5*base15.real)/scale
baseline_total=d['baseline']+baseline_other
actual_other=d['other_exact']-baseline_other
actual_full=d['signal']-baseline_total
mask=x>=1000
metrics={}
pred={}
for T in [20,40,80]:
    other=(.25*recon(base5,z5,T)-.5*recon(base15,z15,T))/scale-baseline_other
    zeta=d['base'].copy()
    for rho in d['zeros']:
        if rho.imag<=T:zeta-=2*np.real(np.exp((rho+1)*np.log(x))/(rho*(rho+1)))
    full=.25*zeta/scale+(other+baseline_other)-baseline_total
    pred[T]=(other,full)
    def rms(a):return float(np.sqrt(np.mean(a[mask]**2)))
    metrics[T]={'other_rms_error':rms(other-actual_other),
                'other_relative_rms_error':rms(other-actual_other)/rms(actual_other),
                'full_rms_error':rms(full-actual_full),
                'full_relative_rms_error':rms(full-actual_full)/rms(actual_full)}
print(json.dumps(metrics,indent=2),flush=True)
assert metrics[80]['full_rms_error']<metrics[20]['full_rms_error']
assert metrics[80]['other_rms_error']<metrics[20]['other_rms_error']
plt.rcParams.update({'font.size':10,'axes.spines.top':False,'axes.spines.right':False})
fig,ax=plt.subplots(2,1,figsize=(11,8),sharex=True,layout='constrained')
for a,actual,col,label in [(ax[0],actual_other,0,'Remaining Dirichlet L-function contribution'),(ax[1],actual_full,1,'Full classes-4-and-11 signal')]:
    a.plot(np.log(x),actual,color='#202020',lw=2,label='Direct prime-power calculation')
    a.plot(np.log(x),pred[20][col],color='#ce8b53',lw=1,label='Numerical zeros with |height| <= 20')
    a.plot(np.log(x),pred[80][col],color='#2776b6',ls='--',lw=1.2,label='Numerical zeros with |height| <= 80')
    a.set_title(label+' — known correction terms removed')
    a.set_ylabel('Corrected smoothed residual / x^(3/2)')
    a.legend(fontsize=9)
    a.grid(alpha=.18);a.axhline(0,color='#bbbbbb',lw=.6)
ax[1].set_xlabel('log x (100 to 1,000,000)')
fig.suptitle('Modulus 15: reconstruction from zeta and Dirichlet L-function zeros',fontsize=14)
fig.savefig(OUT/'mod15_full_reconstruction.png',dpi=170,bbox_inches='tight',pad_inches=.2)
report={'limit':d['LIMIT'],'zero_height_cutoff':80,'conductor5':info5,'conductor15':info15,'metrics':metrics,'elapsed_seconds':time.time()-start,
        'method':'Two critical-line sign-change scans (.25 and .125), root refinement, L residual checks. A .5 scan missed a close pair for conductor 15. Not a certified complete zero list; no off-line zero exclusion. No fitted coefficients. Integrated von Mangoldt weighting and analytic correction terms.'}
(OUT/'full_test_results.json').write_text(json.dumps(report,indent=2))
print('elapsed',time.time()-start,flush=True)
