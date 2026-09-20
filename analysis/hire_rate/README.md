# Hire-rate lab scripts

Thin rem-sieve tooling for H(X), R(X), R_Pois, bin residuals, and lambda-bins.

## Sources

| File | Role |
|------|------|
| `hire_rate_HX.py` + `hire_rate_HX_core.c` | H(X), R(X) table (C core + Python twin) |
| `hire_rate_Rpois.c` | pi(X), R_Pois, E1, E2 at same checkpoints |
| `hire_rate_bin_residual.c` | residual bins by u = log q / log X |
| `hire_rate_lambda_bins.c` | residual re-binned by lambda = Li(X)/(q-1) |

Checked-in `.md` / `.csv` are the lab snapshots through X = 2e10 (or the run that produced them).

## Quick smoke (Python twin)

```bash
cd analysis/hire_rate
python3 hire_rate_HX.py --python --xmax 1e7
```

Expect H(10^7) = 125661.

## Full C table (canyon-scale at 2e10)

```bash
gcc -O3 -march=native -lm hire_rate_HX_core.c -o hire_rate_HX_core
python3 hire_rate_HX.py --xmax 2e10
gcc -O3 -march=native -lm hire_rate_Rpois.c -o hire_rate_Rpois && ./hire_rate_Rpois
gcc -O3 -march=native -lm hire_rate_bin_residual.c -o hire_rate_bin_residual
./hire_rate_bin_residual 10000000
gcc -O3 -march=native -lm hire_rate_lambda_bins.c -o hire_rate_lambda_bins
./hire_rate_lambda_bins 10000000
```

Or from `analysis/`:

```bash
python3 verify_local.py --skip-corridor --hire-c --xmax 10000000
```

Binaries and `*.log` stay untracked.
