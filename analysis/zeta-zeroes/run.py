"""Mod-15 character decomposition and a smoothed zeta-zero reconstruction.
No fitted frequencies or coefficients. Other L-function zeros are not computed.
"""
from pathlib import Path
import json
import numpy as np
import mpmath as mp
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

OUT = Path(__file__).parent
LIMIT = 1_000_000
mp.mp.dps = 30
flags = np.ones(LIMIT + 1, dtype=bool)
flags[:2] = False
for p in range(2, int(LIMIT**.5)+1):
    if flags[p]: flags[p*p::p] = False
lam = np.zeros(LIMIT+1)
for p in np.flatnonzero(flags):
    power = int(p)
    while power <= LIMIT:
        lam[power] = np.log(p)
        power *= int(p)
n = np.arange(LIMIT+1)
unit = (n % 3 != 0) & (n % 5 != 0)
jlookup = np.array([0, 0, 1, 3, 2])  # 2^j modulo 5
chi3 = np.where(n % 3 == 1, 1, -1)
chi5 = np.where(np.isin(n % 5, [1,4]), 1, -1) * unit
chi15 = chi3 * (1j ** jlookup[n % 5]) * unit
door = np.isin(n % 15, [4,11])
assert np.max(np.abs(door - (.25*unit + .25*chi5 - .5*chi15.real))) == 0
x = np.geomspace(100, LIMIT, 1400)
idx = np.floor(x).astype(int)
def integrated(weight):
    values = lam * weight
    a = np.cumsum(values)
    b = np.cumsum(values*n)
    return x*a[idx]-b[idx]
principal = integrated(unit)
quadratic = integrated(chi5)
complex_real = integrated(chi15.real)
actual = integrated(door)
assert np.max(np.abs(actual-(.25*principal+.25*quadratic-.5*complex_real))) < .002
scale = x**1.5
signal = (actual-x*x/8)/scale
zeta_exact = .25*(principal-x*x/2)/scale
other_exact = (.25*quadratic-.5*complex_real)/scale
zeros = [complex(mp.zetazero(i)) for i in range(1,41)]
constant = float(mp.diff(mp.zeta, -1)/mp.zeta(-1))
base = -x*np.log(2*np.pi)+constant
for k in range(1,12):
    base -= x**(1-2*k)/(2*k*(2*k-1))
for p in [3,5]:
    power = p
    while power <= LIMIT:
        base -= np.log(p)*np.maximum(x-power, 0)
        power *= p
def reconstruction(count):
    ans = base.copy()
    for rho in zeros[:count]:
        ans -= 2*np.real(np.exp((rho+1)*np.log(x))/(rho*(rho+1)))
    return .25*ans/scale
rec10, rec40 = reconstruction(10), reconstruction(40)
baseline = .25*base/scale
osc_exact = zeta_exact-baseline
plt.rcParams.update({'font.size':10, 'axes.spines.top':False, 'axes.spines.right':False})
fig, ax = plt.subplots(2,1,figsize=(11,8),sharex=True,layout='constrained')
ax[0].plot(np.log(x), signal, color='#222222', lw=1.6, label='Mod-15 total residual')
ax[0].plot(np.log(x), zeta_exact, color='#2975b5', lw=1.2, label='Exact principal / zeta contribution')
ax[0].plot(np.log(x), other_exact, color='#c46b20', lw=1.2, label='Exact remaining character contribution')
ax[0].set_title('Classes 4 and 11 modulo 15: exact character decomposition')
ax[0].set_ylabel('Smoothed residual / x^(3/2)')
ax[0].legend(loc='best',fontsize=9)
ax[1].plot(np.log(x),osc_exact,color='#222222',lw=2,label='Exact principal signal after known corrections')
ax[1].plot(np.log(x),rec10-baseline,color='#b899cf',lw=1,label='First 10 positive-height zeta zeros + conjugates')
ax[1].plot(np.log(x),rec40-baseline,color='#2975b5',lw=1.1,ls='--',label='First 40 positive-height zeta zeros + conjugates')
ax[1].set_title('Zeta-zero oscillations: known smooth corrections removed; no fitted parameters')
ax[1].set_xlabel('log x (100 to 1,000,000)')
ax[1].set_ylabel('Corrected principal signal / x^(3/2)')
ax[1].legend(loc='best',fontsize=9)
for a in ax: a.axhline(0,color='#bbbbbb',lw=.6); a.grid(alpha=.15)
fig.suptitle('A zeta-zero contribution inside the Hire level q = 5, k = 1',fontsize=14)
fig.savefig(OUT/'mod15_zeta_contribution.png',dpi=170)
mask=x>=1000
print(json.dumps({'limit':LIMIT,'first_zero_height':zeros[0].imag,
    'rms_error_10':float(np.sqrt(np.mean((rec10[mask]-zeta_exact[mask])**2))),
    'rms_error_40':float(np.sqrt(np.mean((rec40[mask]-zeta_exact[mask])**2))),
    'exact_principal_oscillation_rms':float(np.sqrt(np.mean(osc_exact[mask]**2))),
    'active_character_coefficients_before_dividing_by_phi15':{'principal':2,'quadratic_mod5':2,'complex_mod15':-2,'conjugate_mod15':-2}},indent=2))
