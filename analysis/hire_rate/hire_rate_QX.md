# Hire-rate Q_X: finite-Bernoulli zero-deficit scale

## Setup

- Post-process of `hire_rate_tilde_g.csv` (no C re-run).
- Same λ-bins `0.2·2^{k/4}` on frontier `[0.5,4]` (widths ~0.09–0.61;
  near λ∼1 already ~0.15–0.18). Sample sizes (n_q ≥ 2·10^4 at `10^8`,
  ≥ 2·10^6 at `2·10^{10}`) would allow finer bins, but existing geometry
  is already fine enough for the Q diagnosis and matches the tilde_g pack.
- Primary:
  `Q_X(λ) = 2·e^{μ_emp}·g / (μ_emp − Var(N))`
  with `g = e^{-μ_emp} − P0_emp` (= `under` in tilde_g CSV).
- Secondary: same formula with `g_λ = e^{-λ_pred} − P0_emp`.
- Checkpoints: `X ∈ {10^8, 10^9, 10^{10}, 2·10^{10}}`.
- Leading Poisson-binomial asymptotics: if `N=∑ Bern(p_i)`, then
  `μ−Var = Σp_i²` and `g ≈ ½ e^{-μ} Σp_i²` ⇒ **Q → 1** at leading order.
  Leftover `Q−1` is the cubic / higher finite-Bernoulli remainder
  (`∼ (2/3) Σp³/Σp² + …`).

## Room takeaway (three questions)

### 1. Does Q_X sit near 1 on the frontier (esp. λ∼1)?

**Near 1, but systematically high by ~10–12% near λ∼1.**
At `X=2·10^{10}`, bins overlapping λ∼1 give **Q ≈ 1.10–1.12**;
across the whole frontier Q ∈ **[0.98, 1.13]** (mean ≈ 1.08).
So the leading finite-Bernoulli identity is the right scale, but a
stable ~10% leftover remains at mid-λ.

| λ-bin | Q(`10^8`) | Q(`10^9`) | Q(`10^{10}`) | Q(`2·10^{10}`) |
| ---: | ---: | ---: | ---: | ---: |
| [0.4757,0.5657) | 1.1535 | 1.1384 | 1.1291 | 1.1253 |
| [0.5657,0.6727) | 1.1494 | 1.1408 | 1.1268 | 1.1245 |
| [0.6727,0.8000) | 1.1694 | 1.1423 | 1.1324 | 1.1266 |
| [0.8000,0.9514) | 1.1311 | 1.1470 | 1.1247 | 1.1223 |
| [0.9514,1.1314) | 1.1513 | 1.1335 | 1.1202 | 1.1169 |
| [1.1314,1.3454) | 1.1217 | 1.1270 | 1.1113 | 1.1079 |
| [1.3454,1.6000) | 1.0875 | 1.1042 | 1.1044 | 1.1008 |
| [1.6000,1.9027) | 1.1016 | 1.1089 | 1.0891 | 1.0822 |
| [1.9027,2.2627) | 1.0884 | 1.0758 | 1.0673 | 1.0577 |
| [2.2627,2.6909) | 1.0599 | 1.0465 | 1.0342 | 1.0340 |
| [2.6909,3.2000) | 1.0549 | 1.0298 | 1.0114 | 1.0020 |
| [3.2000,3.8055) | 0.9464 | 0.9740 | 0.9764 | 0.9822 |

Near λ∼1 at largest X:

| λ-bin | μ | under | μ−Var | **Q** | Q_λ |
| ---: | ---: | ---: | ---: | ---: | ---: |
| [0.8000,0.9514) | 0.8204 | +0.03849 | 0.1558 | **1.1223** | 0.4844 |
| [0.9514,1.1314) | 1.0235 | +0.04126 | 0.2056 | **1.1169** | 0.9931 |
| [1.1314,1.3454) | 1.2217 | +0.04169 | 0.2553 | **1.1079** | 1.0245 |
| [1.3454,1.6000) | 1.4325 | +0.04046 | 0.3080 | **1.1008** | 0.8894 |

### 2. Does Q collapse across X?

**Yes — extremely.** Cosine of the 12-bin Q vector vs `X=2·10^{10}` is
**≥ 0.9998 already at `10^8`**. Absolute values drift slowly toward 1
(frontier mean 1.101 → 1.082 from `10^8` → `2·10^{10}`), consistent with
effective `p_i` shrinking, but the *shape* is locked.

| X | cosine Q | mean Q | min | max |
| ---: | ---: | ---: | ---: | ---: |
| $10^8$ | 0.999783 | 1.1013 | 0.9464 | 1.1694 |
| $10^9$ | 0.999963 | 1.0974 | 0.9740 | 1.1470 |
| $10^{10}$ | 0.999994 | 1.0856 | 0.9764 | 1.1324 |
| $2\cdot10^{10}$ | 1.000000 | 1.0819 | 0.9822 | 1.1266 |

### 3. Where Q departs from 1: leftover after finite-Bernoulli correction?

**Yes — a smooth, λ-dependent leftover after the leading Σp² correction.**

- **Low–mid λ ([0.5,2)):** Q ≈ **1.10–1.13** (leftover ~10–13%).
- **High λ ([2,4)):** Q drifts down to **≈ 0.98–1.05**, closer to 1.
- Leftover shrinks slowly with X (nq-weighted ⟨|Q−1|⟩ on [0.5,1):
  0.152 → 0.125; on [2,4): 0.067 → 0.031).
- This matches the next-order Poisson-binomial expansion:
  `Q ≈ 1 + (2/3)(Σp³)/(Σp²) + (Σp²)/4 + ⋯`, not a failure of the
  Bernoulli-sum picture. Secondary `Q_λ` is noisier / less stable
  (λ_pred ≠ μ_emp), so primary-vs-μ is the right diagnostic.

| X | band | ⟨Q⟩ (nq-wt) | ⟨|Q−1|⟩ |
| ---: | ---: | ---: | ---: |
| $10^8$ | [0.5,1) | 1.1517 | 0.1517 |
| $10^8$ | [1,2) | 1.1193 | 0.1193 |
| $10^8$ | [2,4) | 1.0458 | 0.0665 |
| $10^9$ | [0.5,1) | 1.1416 | 0.1416 |
| $10^9$ | [1,2) | 1.1204 | 0.1204 |
| $10^9$ | [2,4) | 1.0380 | 0.0480 |
| $10^{10}$ | [0.5,1) | 1.1284 | 0.1284 |
| $10^{10}$ | [1,2) | 1.1083 | 0.1083 |
| $10^{10}$ | [2,4) | 1.0283 | 0.0374 |
| $2\cdot10^{10}$ | [0.5,1) | 1.1248 | 0.1248 |
| $2\cdot10^{10}$ | [1,2) | 1.1042 | 0.1042 |
| $2\cdot10^{10}$ | [2,4) | 1.0243 | 0.0311 |

## Detail at `X = 2·10^{10}` (frontier)

| λ_lo | λ_hi | n_q | μ | under | μ−Var | Var/μ | **Q** | Q_λ |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 0.4757 | 0.5657 | 13880594 | 0.4994 | +0.02936 | 0.0860 | 0.8278 | **1.1253** | 0.6932 |
| 0.5657 | 0.6727 | 11769442 | 0.5667 | +0.03155 | 0.0989 | 0.8255 | **1.1245** | 0.1486 |
| 0.6727 | 0.8000 | 9977673 | 0.7205 | +0.03680 | 0.1343 | 0.8136 | **1.1266** | 0.9455 |
| 0.8000 | 0.9514 | 8461515 | 0.8204 | +0.03849 | 0.1558 | 0.8101 | **1.1223** | 0.4844 |
| 0.9514 | 1.1314 | 7175408 | 1.0235 | +0.04126 | 0.2056 | 0.7991 | **1.1169** | 0.9931 |
| 1.1314 | 1.3454 | 6083826 | 1.2217 | +0.04169 | 0.2553 | 0.7910 | **1.1079** | 1.0245 |
| 1.3454 | 1.6000 | 5160298 | 1.4325 | +0.04046 | 0.3080 | 0.7850 | **1.1008** | 0.8894 |
| 1.6000 | 1.9027 | 4376336 | 1.6998 | +0.03724 | 0.3767 | 0.7784 | **1.0822** | 0.8585 |
| 1.9027 | 2.2627 | 3712406 | 2.0344 | +0.03233 | 0.4675 | 0.7702 | **1.0577** | 0.8976 |
| 2.2627 | 2.6909 | 3149495 | 2.4471 | +0.02604 | 0.5819 | 0.7622 | **1.0340** | 0.9739 |
| 2.6909 | 3.2000 | 2671549 | 2.8899 | +0.01959 | 0.7036 | 0.7565 | **1.0020** | 0.8873 |
| 3.2000 | 3.8055 | 2266916 | 3.4581 | +0.01337 | 0.8647 | 0.7499 | **0.9822** | 0.9192 |

## Method notes

- Source columns from `hire_rate_tilde_g.csv`: `mu_emp`, `var_N`, `under`
  (`= e^{-μ}−P0`), `g` (`= e^{-λ}−P0`), `P0_emp`, `n_q`.
- No Mathlib; no git push; C unnamed / not re-run; papers frozen; X not extended.
- Mac path `/Users/halfasecond/e-walk-app/analysis/hire_rate/` not mounted — artifacts left under `drafts/`.

## Artifacts

- `drafts/hire_rate_QX.csv` — long form with Q, Q_lam, mu_minus_var, under, …
- `drafts/hire_rate_QX.md` — this note
- Inputs: `drafts/hire_rate_tilde_g.csv` / `.md` / `.c`
