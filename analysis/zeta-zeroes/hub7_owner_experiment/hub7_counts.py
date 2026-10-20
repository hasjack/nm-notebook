"""Ordinary Hire counts at hub 7 via the fixed mod-21 character expansion.
Numerical critical-line roots are not a certified complete zero list.
Fast Euler--Maclaurin scans are checked against mpmath, then roots refined.
Uses an exact count anchor at x=100 and exact higher-prime-power corrections.
"""
from pathlib import Path
import json,time,math
import numpy as np
import mpmath as mp
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from scipy.special import loggamma,expi
from scipy.integrate import cumulative_trapezoid

OUT=Path(__file__).parent;LIMIT=1_000_000;START=100;TMAX=80
mp.mp.dps=30
begin=time.time()
# Mod 7 generator 3: powers 1,3,2,6,4,5.
js={1:0,3:1,2:2,6:3,4:4,5:5}
def character(f,b,twist3):
    return [mp.mpc(0) if a%7==0 or (twist3 and a%3==0) else
      (1 if not twist3 or a%3==1 else -1)*mp.exp(2j*mp.pi*b*js[a%7]/6)
      for a in range(f)]
chars={'cubic7':character(7,2,False),
       'quadratic21':character(21,3,True),
       'complex21':character(21,1,True)}
for chi in chars.values():
    f=len(chi)
    assert abs(chi[-1]-1)<mp.mpf('1e-25')
    for a in range(f):
        for b in range(f):assert abs(chi[(a*b)%f]-chi[a]*chi[b])<mp.mpf('1e-25')

def fast_L(s,chi):
    # Hurwitz-zeta Euler--Maclaurin with N=80, 14 Bernoulli terms.
    f=len(chi);ans=np.zeros_like(s,dtype=complex)
    for a in range(1,f):
        if abs(chi[a])<1e-20:continue
        alpha=a/f;N=80;u=N+alpha
        z=np.sum(np.exp(-s[:,None]*np.log(np.arange(N)+alpha)),axis=1)
        z+=np.exp((1-s)*np.log(u))/(s-1)+.5*np.exp(-s*np.log(u))
        rising=s.copy()
        for k in range(1,15):
            if k>1:rising*=(s+2*k-3)*(s+2*k-2)
            c=float(mp.bernoulli(2*k)/mp.factorial(2*k))
            z+=c*rising*np.exp((-s-2*k+1)*np.log(u))
        ans+=complex(chi[a])*z
    return ans*np.exp(-s*np.log(f))

def zeros_for(name,chi):
    path=OUT/(name+'_roots.json')
    if path.exists():
        data=json.loads(path.read_text())
        if data['cutoff']==TMAX:return data
    f=len(chi)
    tau=sum(chi[a]*mp.exp(2j*mp.pi*a/f) for a in range(f))
    W=tau/mp.sqrt(f)
    assert abs(abs(W)-1)<mp.mpf('1e-25')
    phase=mp.exp(-.5j*mp.arg(W))
    real_char=name=='quadratic21'
    lo=0 if real_char else -TMAX
    step=.125
    while True:
        grid=np.arange(lo,TMAX+step/2,step)
        s=.5+1j*grid
        lv=fast_L(s,chi)
        errors=[]
        for i in np.linspace(0,len(grid)-1,17,dtype=int):
            ref=complex(mp.dirichlet(mp.mpc(.5,float(grid[i])),chi))
            errors.append(abs(ref-lv[i])/(1+abs(ref)))
        assert max(errors)<1e-10,max(errors)
        rotated=lv*np.exp(1j*(grid*np.log(f/np.pi)/2+loggamma(s/2).imag))*complex(phase)
        assert np.max(np.abs(rotated.imag))<1e-9
        vals=rotated.real
        def intervals(stride):
            return [(grid[i],grid[i+stride]) for i in range(0,len(grid)-stride,stride) if vals[i]*vals[i+stride]<0]
        coarse,fine=intervals(2),intervals(1)
        print(name,'scan',step*2,len(coarse),step,len(fine),flush=True)
        if len(coarse)==len(fine):break
        step/=2
        assert step>=.015625
    def hardy(t):
        s=mp.mpf('.5')+1j*t
        factor=mp.power(f/mp.pi,s/2)*mp.gamma(s/2)
        return mp.re(phase*factor*mp.dirichlet(s,chi)/abs(factor))
    heights=[];residual=mp.mpf(0)
    for a,b in fine:
        root=mp.findroot(hardy,(mp.mpf(float(a)),mp.mpf(float(b))),solver='anderson',tol=mp.mpf('1e-23'))
        assert a<root<b
        residual=max(residual,abs(mp.dirichlet(mp.mpf('.5')+1j*root,chi)))
        heights.append(float(root))
    assert residual<mp.mpf('1e-18'),residual
    if real_char:heights=sorted([-v for v in heights]+heights)
    data={'cutoff':TMAX,'heights':heights,'scan_step':step,
      'scan_count':len(fine),'max_root_residual':float(residual),'max_scan_relative_error':max(errors)}
    path.write_text(json.dumps(data,indent=2))
    print(name,'refined',len(heights),'residual',float(residual),flush=True)
    return data
root_data={name:zeros_for(name,chi) for name,chi in chars.items()}
zeta=[complex(mp.zetazero(i)) for i in range(1,41)]
zeta+= [z.conjugate() for z in zeta]

flags=np.ones(LIMIT+1,dtype=bool);flags[:2]=False
for p in range(2,int(LIMIT**.5)+1):
    if flags[p]:flags[p*p::p]=False
primes=np.flatnonzero(flags)
owners=primes[np.isin(primes%21,[8,13])]
residues=np.arange(21)
principal=((residues%3!=0)&(residues%7!=0)).astype(float)
ch7=np.array([complex(chars['cubic7'][int(a%7)]) if a%3 else 0j for a in residues])
ch21r=np.array([complex(v) for v in chars['quadratic21']])
ch21c=np.array([complex(v) for v in chars['complex21']])
decomp=principal/6+ch7.real/3-ch21r.real/6-ch21c.real/3
assert np.max(abs(decomp-np.isin(residues,[8,13])))<1e-14
corrections=[]
for p in primes[primes<=int(LIMIT**.5)]:
    power=int(p)*int(p);j=2
    while power<=LIMIT:
        if power%21 in [8,13]:corrections.append((power,1/j))
        power*=int(p);j+=1
corrections.sort()
positions=np.array([p for p,w in corrections]);cum=np.cumsum([w for p,w in corrections])
def high_power_correction(t):
    inds=np.searchsorted(positions,t,side='right')-1
    return np.where(inds>=0,cum[np.maximum(inds,0)],0)
constants={}
for name,chi in chars.items():
    first=mp.diff(lambda s:mp.dirichlet(s,chi),0)
    second=mp.diff(lambda s:mp.dirichlet(s,chi),0,2)
    constants[name]=complex(second/(2*first))

def calculate(points):
    t=np.geomspace(START,LIMIT,points);logt=np.log(t)
    count=np.searchsorted(owners,t,side='right');C0=int(count[0])
    correction=high_power_correction(t)
    euler0=np.zeros_like(t);euler7=np.zeros_like(t,dtype=complex)
    for p in [3,7]:
        power=p;j=1
        while power<=LIMIT:
            euler0+=np.log(p)*(t>=power)
            if p==3:euler7+=np.log(p)*complex(chars['cubic7'][3]**j)*(t>=power)
            power*=p;j+=1
    trivial=-.5*np.log1p(-t**-2)
    base0=-np.log(2*np.pi)+trivial-euler0
    bases={name:-b-logt+trivial for name,b in constants.items()}
    bases['cubic7']-=euler7
    def psi(base,roots,cut):
        out=np.asarray(base,dtype=complex).copy()
        for rho in roots:
            if abs(rho.imag)<=cut:out-=np.exp(rho*logt)/rho
        return out.real
    reference=C0+(expi(logt)-expi(np.log(START)))/6
    predictions={};metrics={}
    for cut in [0,20,40,80]:
        ps={name:psi(bases[name],[complex(.5,v) for v in root_data[name]['heights']],cut) for name in chars}
        estimate=(t+psi(base0,zeta,cut))/6+ps['cubic7']/3-ps['quadratic21']/6-ps['complex21']/3
        integral=cumulative_trapezoid(estimate/logt**2,logt,initial=0)
        pred=C0+estimate/logt-estimate[0]/logt[0]+integral-(correction-correction[0])
        predictions[cut]=pred
        mask=t>=1000
        err=float(np.sqrt(np.mean((pred[mask]-count[mask])**2)))
        resrms=float(np.sqrt(np.mean((count[mask]-reference[mask])**2)))
        metrics[cut]={'rms_count_error':err,'rms_error_relative_to_residual':err/resrms,
          'endpoint_predicted':float(pred[-1]),'endpoint_actual':int(count[-1])}
    return t,count,reference,predictions,metrics
t,c,ref,pred,metrics=calculate(65537)
t2,c2,ref2,pred2,metrics2=calculate(131073)
grid_error=float(np.sqrt(np.mean((pred[80]-pred2[80][::2])**2)))
assert grid_error<.05,grid_error
print(json.dumps(metrics2,indent=2),flush=True)
print('integration_grid_error',grid_error,'elapsed',time.time()-begin,flush=True)
fig,ax=plt.subplots(2,1,figsize=(11,8),sharex=True,layout='constrained')
stride=32
for a,series,shift,title in [(ax[0],c2,0,'Ordinary owners: classes 8 and 13 modulo 21'),(ax[1],c2-ref2,ref2,'Fluctuations around the anchored Li(x)/6 baseline')]:
    a.plot(np.log(t2[::stride]),series[::stride],color='#202020',lw=1.8,label='Direct prime-owner count')
    a.plot(np.log(t2[::stride]),(pred2[20]-shift)[::stride],color='#cf8b4e',lw=1,label='Zero-height cutoff 20')
    a.plot(np.log(t2[::stride]),(pred2[80]-shift)[::stride],color='#2776b6',ls='--',lw=1.1,label='Zero-height cutoff 80')
    a.set_title(title);a.grid(alpha=.18);a.legend(fontsize=9)
    a.set_ylabel('Owners' if a==ax[0] else 'Count minus baseline')
ax[1].set_xlabel('log x (100 to 1,000,000)')
fig.suptitle('Hub 7: reconstruction from predetermined zeta and L-function coefficients',fontsize=14)
fig.savefig(OUT/'hub7_ordinary_owner_counts.png',dpi=170,bbox_inches='tight',pad_inches=.2)
report={'limit':LIMIT,'modulus':21,'classes':[8,13],
 'character_expansion':'principal/6 + Re(cubic conductor7)/3 - quadratic conductor21/6 - Re(complex conductor21)/3',
 'roots':root_data,'metrics':metrics2,'integration_grid_rms_difference':grid_error,
 'anchor':{'x':START,'owner_count':int(np.searchsorted(owners,START,side='right'))},
 'method':'Exact initial-count anchor and exact higher-prime-power corrections. Numerical critical-line zeros; no completeness or off-line-zero certification. Fixed character coefficients, no fitted amplitudes or frequencies.'}
(OUT/'hub7_results.json').write_text(json.dumps(report,indent=2))
