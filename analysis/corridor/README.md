# M31 corridor thin scripts

Best-practice verify for the Islands / Paper 2 corridor integers.

```bash
cd analysis/corridor
python3 verify_best_practice.py
python3 verify_best_practice.py --gp
python3 verify_best_practice.py --skip-mixed
python3 verify_best_practice.py --skip-tau-v
```

Ascending: hand door checks → `thin_owners.py 31` → `M31_mixed_connectors.py` → `thin_owner_of_q.py` for tau(v).
