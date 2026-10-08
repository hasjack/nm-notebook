"""Two-door difference: exact arithmetic vs cached numerical character zeros.
Uses integrated Mangoldt weighting. Zero real parts are inputs, not proved.
No fitted coefficients. Self-contained cached height list embedded below.
"""
from pathlib import Path
import json
import numpy as np
import mpmath as mp
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
HEIGHTS = [-79.40133001329508, -78.46906481955283, -77.49587645427535, -76.16228435333949, -74.85134573755627, -73.10864317241439, -72.22103698966299, -70.9320573691847, -70.07174416610219, -68.43292678782248, -68.08987964036393, -66.1794309146137, -64.80545124688224, -63.27891447806202, -62.3797948831763, -61.20179238520012, -59.993115025944235, -58.89217832316914, -57.71177035079456, -55.70923174933811, -54.722734046088846, -53.10896654979426, -52.39708791002574, -50.9967324841521, -49.79259749574019, -48.64349190291977, -46.570990259677835, -45.43459916509606, -44.08858944865197, -42.88707262799532, -41.80834998501417, -40.40724799364991, -39.029944901987854, -36.85300610546312, -35.99118413573697, -34.37951273486247, -33.29702889306198, -31.997741203596537, -30.519345891473563, -28.552716527179815, -26.796235597002106, -25.89258884644111, -24.071858315178684, -23.14894539492477, -21.28464369710185, -19.13784242419278, -17.44476426609567, -16.17189288498984, -14.464461134463344, -13.02895627399164, -10.326204250314941, -8.264501653903425, -6.590782670215471, -4.406700239803674, 2.7346037091188373, 5.24301049275449, 8.414685249804899, 10.187602727645302, 11.907372476546671, 13.33739585541559, 15.366139576497782, 17.772390249216663, 18.976999650088253, 20.62763177596965, 21.883973024208913, 23.338480017759878, 25.388027880177475, 27.194731626897173, 28.398977143837058, 29.66537127834534, 31.192356563675382, 32.15849090668378, 34.25977663837223, 35.81987910298116, 37.22297310571034, 38.279684105962176, 39.61717684267314, 40.869737495824005, 42.12516342957912, 44.3203058936473, 45.16648265242354, 46.96022538488976, 47.53076548769255, 49.11332039937922, 50.14343032831144, 51.58686129217962, 53.505263485840935, 54.55621928858429, 55.70764458372943, 57.15833992509121, 57.800308204221786, 59.366053654587795, 60.48747463761089, 62.346811172150915, 63.589650637547265, 64.5279786390767, 65.84403544176426, 66.91280088660251, 67.90022363419274, 69.28181954768564, 70.84473892530416, 72.21093245048998, 73.50317406268644, 74.12058006765719, 75.74426525636136, 76.46370925336944, 77.65912964416677, 79.16488689447043]
OUT=Path(__file__).parent
LIMIT=1_000_000
mp.mp.dps=25
chi=[0 if a%3==0 or a%5==0 else (1 if a%3==1 else -1)*{1:1,2:1j,3:-1j,4:-1}[a%5] for a in range(15)]
L=lambda s:mp.dirichlet(s,chi)
residual=max(float(abs(L(mp.mpc(.5,t)))) for t in HEIGHTS)
assert residual<1e-10
sieve=np.ones(LIMIT+1,bool);sieve[:2]=False
for p in range(2,int(LIMIT**.5)+1):
 if sieve[p]:sieve[p*p::p]=False
primes=np.flatnonzero(sieve)
lam=np.zeros(LIMIT+1)
for p in primes:
 power=int(p)
 while power<=LIMIT:
  lam[power]=np.log(p);power*=int(p)
n=np.arange(LIMIT+1)
K=((n%3==1)&(n%5==4))|((n%3==2)&(n%5==1))
D=((n%3==1)&(n%5==1))|((n%3==2)&(n%5==4))
delta=K.astype(int)-D.astype(int)
C=np.array(chi)[n%15]
assert np.array_equal(delta,-C.real)
x=np.geomspace(100,LIMIT,1400);idx=np.floor(x).astype(int);scale=x**1.5
v=lam*delta
exact=x*np.cumsum(v)[idx]-np.cumsum(n*v)[idx]
first=mp.diff(L,0);second=mp.diff(L,0,2)
b=complex(second/(2*first));constant=complex(mp.diff(L,-1)/L(-1))
base=x*(1-b-np.log(x))+constant
for k in range(1,12):base-=x**(1-2*k)/(2*k*(2*k-1))
# The door difference is minus the real part of the C-weighted sum.
correction=-base.real
actual=(exact-correction)/scale
pred={};metrics={};mask=x>=1000
rms=lambda y:float(np.sqrt(np.mean(y[mask]**2)))
for cutoff in [20,40,80]:
 wave=np.zeros(len(x),complex)
 selected=[t for t in HEIGHTS if abs(t)<=cutoff]
 for t in selected:
  rho=complex(.5,t)
  wave+=np.exp((rho+1)*np.log(x))/(rho*(rho+1))
 pred[cutoff]=wave.real/scale
 metrics[cutoff]={'zeros_used':len(selected),'rms_error':rms(pred[cutoff]-actual),'relative_rms_error':rms(pred[cutoff]-actual)/rms(actual)}
assert metrics[80]['rms_error']<metrics[20]['rms_error']
plt.rcParams.update({'font.size':11,'axes.spines.top':False,'axes.spines.right':False})
fig,axes=plt.subplots(2,1,figsize=(11,7),sharex=True,layout='constrained',gridspec_kw={'height_ratios':[2,1]})
axes[0].plot(np.log(x),actual,color='#222222',lw=2,label='Exact kept − discarded arithmetic')
axes[0].plot(np.log(x),pred[20],color='#b77530',lw=1,label='Character zeros: |height| ≤ 20')
axes[0].plot(np.log(x),pred[80],color='#2374a6',ls='--',lw=1.3,label='Character zeros: |height| ≤ 80')
axes[0].set_ylabel('Corrected smoothed signal / x^(3/2)');axes[0].legend(fontsize=9)
axes[1].plot(np.log(x),pred[80]-actual,color='#2374a6',lw=1);axes[1].set_ylabel('Reconstruction error');axes[1].set_xlabel('log x · x from 100 to 1,000,000')
for ax in axes:ax.axhline(0,color='#aaaaaa',lw=.7);ax.grid(alpha=.18)
fig.suptitle('Hire 5: subtracting the doors isolates the complex character modulo 15\nKnown analytic and trivial-zero corrections removed; no fitted coefficients',fontsize=13)
fig.savefig(OUT/'door_difference.png',dpi=170)
report={'limit':LIMIT,'observable':'sum_{n<=x} Lambda(n) (K(n)-D(n)) (x-n)','identity':'K-D = -Re(chi3*psi5)','zero_count':len(HEIGHTS),'cached_zero_max_residual_rechecked':residual,'metrics':metrics,'limitations':'Numerical critical-line zero list; not certified complete. beta=1/2 is an input. Integrated weighted observable, not raw prime counts. Relative RMS measured for x>=1000 after correction removal.'}
(OUT/'door_difference_results.json').write_text(json.dumps(report,indent=2))
print(json.dumps(report,indent=2))
