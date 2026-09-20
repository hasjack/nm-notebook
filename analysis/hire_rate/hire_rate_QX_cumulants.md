# Hire-rate Q_X cumulants: T-collapse, Q_2nd, sign fingerprint

## Setup

- Small unnamed C extension `hire_rate_cumulants.c` of the tilde_g rem-sieve:
  stores exact factorial moments
  `m2=E[N(N-1)]`, `m3=E[N(N-1)(N-2)]`, `m4=E[N(N-1)(N-2)(N-3)]`
  (occupancy `P(N=0,1,2,≥3)` alone cannot pin κ₃/κ₄).
- Fine λ-bins: `0.5·2^{k/4}` on `[0.5,4]` (12 bins).
- Checkpoints: `X ∈ {10^8, 10^9, 10^{10}, 2·10^{10}}`.
- Wall: **988 s** through `2·10^{10}` (RSS ~895 MB); in-band `sat_cells=0`.
- Derived (occupancy / moments only — **no P0 in the Q₂ predictor**):
  - `S2_hat = μ − Var = −κ₂^(F)` (= `Σ p_i²` for Poisson-binomial)
  - `κ₃^(F) = m3 − 3 m2 μ + 2 μ³`, `S3_hat = κ₃^(F)/2` (= `Σ p_i³`)
  - `κ₄^(F) = m4 − 4 m3 μ − 3 m2² + 12 m2 μ² − 6 μ⁴`
  - `Q = 2 e^{μ} · under / S2` with `under = e^{-μ} − P0`
  - `T_X(λ) = (Q(λ)−1)·log X`
  - `Q_2nd ≈ 1 + (2/3)(S3/S2) − S2/4`

Papers frozen; no Mathlib; not bigger X.

## Room takeaway (three diagnostics)

### 1. Does `T_X = (Q−1) log X` sit near ~1.9 across decades near `λ∼1`?

**No as a universal constant near λ∼1 — yes as a frontier-mean scale.**
Near `λ∼1` (bins overlapping `[0.8,1.4]`), `T` sits at
**≈ 2.5–2.8** and is stable across decades (mean `T` ≈ **2.52 → 2.78**
from `10^8 → 2·10^{10}`), not ~1.9.
Across the whole frontier `[0.5,4]`, mean `T` is **≈ 1.7–1.9**
(closer to the ~1.9 figure), but that average mixes a mid-λ hump
`T≈2.5–3` with a high-λ fade `T→0` (and a slightly negative bin at
`λ≳3.3` where `Q<1`).

**Name the scaling function, not a constant:**
`Q_X(λ) − 1 ≈ T(λ) / log X` with a stable shape `T(λ)` peaked near
`λ∼1` at `T≈2.5–2.8`, falling toward 0 as `λ→4`. Cosine of the
12-bin `T` vector vs `X=2·10^{10}` is **≥ 0.95 already at `10^8` (≥ 0.996 for `X≥10^9`)**.

| X | mean T near λ∼1 | min | max | frontier mean T | cosine T |
| ---: | ---: | ---: | ---: | ---: | ---: |
| $10^8$ | 2.519 | 2.062 | 2.777 | 1.700 | 0.9527 |
| $10^9$ | 2.830 | 2.502 | 3.068 | 1.941 | 0.9970 |
| $10^{10}$ | 2.775 | 2.537 | 3.015 | 1.856 | 0.9967 |
| $2·10^{10}$ | 2.779 | 2.504 | 2.999 | 1.843 | 1.0000 |

### 2. Does `Q_2nd` from `(S2,S3)` match observed `Q`?

**Yes — closely on the frontier, especially mid-λ.**
Predictor uses **only** `S2=μ−Var` and `S3=κ₃^(F)/2` (no P0).
At `X=2·10^{10}`, `|Q − Q_2nd|` has frontier mean **≈ 0.011**
(max **0.018**);
near `λ∼1`, `Q ≈ 1.117` vs `Q_2nd ≈ 1.101`
(typical residual ~0.01–0.03). Cosine`(Q, Q_2nd)` ≥ **0.999** at every X.
The alternate sign `+ S2/4` (from an earlier QX note) overshoots badly —
the Heavy formula with **− S2/4** is the one that matches.

So the ~10% leftover `Q−1` is quantitatively the cubic finite-Bernoulli
remainder: a **scaling function** `Q_2nd(λ) = 1 + (2/3) S3(λ)/S2(λ) − S2(λ)/4`,
not a constant shift.

### 3. Sign fingerprint `κ₂^(F)<0`, `κ₃^(F)>0`, `κ₄^(F)<0`?

**Yes — on every frontier bin at every X.**
`48/48` bins satisfy
`(κ₂, κ₃, κ₄) = (−, +, −)`. This is exactly the Poisson-binomial /
heterogeneous-Bernoulli fingerprint
`κ_r^(F) = (−1)^{r−1}(r−1)! Σ p_i^r`.

## `T_X(λ)` by fine bin

| λ-bin | $T(10^8)$ | $T(10^9)$ | $T(10^{10})$ | $T(2·10^{10})$ |
| ---: | ---: | ---: | ---: | ---: |
| [0.5000,0.5946) | +2.794 | +2.948 | +2.985 | +3.002 |
| [0.5946,0.7071) | +3.022 | +2.933 | +2.884 | +2.974 |
| [0.7071,0.8409) | +2.777 | +3.024 | +3.015 | +2.999 |
| [0.8409,1.0000) | +2.582 | +3.068 | +2.824 | +2.850 |
| [1.0000,1.1892) | +2.655 | +2.728 | +2.726 | +2.763 |
| [1.1892,1.4142) | +2.062 | +2.502 | +2.537 | +2.504 |
| [1.4142,1.6818) | +1.398 | +2.434 | +2.259 | +2.285 |
| [1.6818,2.0000) | +2.264 | +1.749 | +1.980 | +1.769 |
| [2.0000,2.3784) | +1.491 | +1.451 | +1.329 | +1.233 |
| [2.3784,2.8284) | +0.763 | +0.965 | +0.560 | +0.614 |
| [2.8284,3.3636) | +0.934 | -0.213 | +0.220 | -0.214 |
| [3.3636,4.0000) | -2.342 | -0.296 | -1.052 | -0.669 |

## Detail at `X = 2·10^{10}`: Q vs Q_2nd, T, S2, S3

| λ-bin | μ | S2 | S3 | Q | Q_2nd | Q−Q_2nd | T |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| [0.5000,0.5946) | 0.5005 | 0.0865 | 0.0169 | 1.1266 | 1.1087 | +0.0179 | +3.002 |
| [0.5946,0.7071) | 0.6083 | 0.1103 | 0.0224 | 1.1254 | 1.1075 | +0.0179 | +2.974 |
| [0.7071,0.8409) | 0.7549 | 0.1438 | 0.0310 | 1.1264 | 1.1079 | +0.0185 | +2.999 |
| [0.8409,1.0000) | 0.8855 | 0.1684 | 0.0367 | 1.1201 | 1.1033 | +0.0169 | +2.850 |
| [1.0000,1.1892) | 1.0648 | 0.2149 | 0.0495 | 1.1165 | 1.1000 | +0.0165 | +2.763 |
| [1.1892,1.4142) | 1.2752 | 0.2752 | 0.0666 | 1.1056 | 1.0925 | +0.0131 | +2.504 |
| [1.4142,1.6818) | 1.5043 | 0.3302 | 0.0822 | 1.0963 | 1.0834 | +0.0130 | +2.285 |
| [1.6818,2.0000) | 1.8008 | 0.4092 | 0.1047 | 1.0746 | 1.0683 | +0.0063 | +1.769 |
| [2.0000,2.3784) | 2.1539 | 0.4960 | 0.1307 | 1.0520 | 1.0517 | +0.0003 | +1.233 |
| [2.3784,2.8284) | 2.5572 | 0.6154 | 0.1681 | 1.0259 | 1.0283 | -0.0024 | +0.614 |
| [2.8284,3.3636) | 3.0452 | 0.7480 | 0.2089 | 0.9910 | 0.9992 | -0.0082 | -0.214 |
| [3.3636,4.0000) | 3.6414 | 0.9188 | 0.2743 | 0.9718 | 0.9693 | +0.0024 | -0.669 |

## Sign fingerprint at `X = 2·10^{10}`

| λ-bin | κ₂^(F) | κ₃^(F) | κ₄^(F) | signs (−,+,−)? |
| ---: | ---: | ---: | ---: | :---: |
| [0.5000,0.5946) | -8.6461e-02 | +3.3792e-02 | -2.1105e-02 | yes |
| [0.5946,0.7071) | -1.1034e-01 | +4.4724e-02 | -2.8955e-02 | yes |
| [0.7071,0.8409) | -1.4383e-01 | +6.2091e-02 | -4.2888e-02 | yes |
| [0.8409,1.0000) | -1.6843e-01 | +7.3461e-02 | -5.0964e-02 | yes |
| [1.0000,1.1892) | -2.1490e-01 | +9.9092e-02 | -7.2962e-02 | yes |
| [1.1892,1.4142) | -2.7516e-01 | +1.3313e-01 | -1.0068e-01 | yes |
| [1.4142,1.6818) | -3.3025e-01 | +1.6439e-01 | -1.3164e-01 | yes |
| [1.6818,2.0000) | -4.0917e-01 | +2.0937e-01 | -1.6953e-01 | yes |
| [2.0000,2.3784) | -4.9597e-01 | +2.6140e-01 | -2.0573e-01 | yes |
| [2.3784,2.8284) | -6.1538e-01 | +3.3622e-01 | -2.9879e-01 | yes |
| [2.8284,3.3636) | -7.4804e-01 | +4.1781e-01 | -3.6794e-01 | yes |
| [3.3636,4.0000) | -9.1876e-01 | +5.4857e-01 | -5.9494e-01 | yes |

## Cross-X summary: Q vs Q_2nd residuals

| X | mean abs(Q−Q₂) | max abs(Q−Q₂) | mean abs(rel) | cosine(Q,Q₂) | #sign-OK |
| ---: | ---: | ---: | ---: | ---: | ---: |
| $10^8$ | 0.0246 | 0.0633 | 0.0233 | 0.999711 | 12/12 |
| $10^9$ | 0.0163 | 0.0276 | 0.0146 | 0.999973 | 12/12 |
| $10^{10}$ | 0.0123 | 0.0203 | 0.0111 | 0.999971 | 12/12 |
| $2·10^{10}$ | 0.0111 | 0.0185 | 0.0101 | 0.999969 | 12/12 |

## Paste-ready room takeaway

**T collapse?** Shape-yes / constant-no. `T(λ)=(Q−1)log X` is a stable
**function of λ**: peaked `T≈2.5–2.8` near `λ∼1` across `10^8…2·10^{10}`
(not the ~1.9 figure — that only appears as a frontier-wide average).
So write `Q_X(λ)=1 + T(λ)/log X`, not `Q≈1+c/log X`.

**Q_2nd match?** Yes. From occupancy-side moments alone,
`Q_2nd=1+(2/3)(S3/S2)−S2/4` tracks observed `Q` to ~0.01–0.03 near
`λ∼1` (cosine ≥0.999). The leftover is the cubic Bernoulli remainder,
a **scaling function of λ**, not a constant.

**Sign fingerprint?** Yes everywhere on the frontier:
`κ₂^(F)<0`, `κ₃^(F)>0`, `κ₄^(F)<0` — Poisson-binomial, not Poisson.
