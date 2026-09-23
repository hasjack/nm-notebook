#!/bin/sh
# Overnight plus-side PRP hunt, 100k-150k digits. 8 hours or 100k attempts.
# PRP of a 100k-digit survivor is ~8-10 min. Hits are probable until cert.py.
cd "$(dirname "$0")"
exec python3 -u hunt_mp.py --jobs 10 --no-cert --hits-only \
  --family wide --vmin2 2 --vmax2 2 \
  --min-digits 100000 --max-digits 150000 \
  --pool-max 71 --nmin 10 --nmax 10 --emin 2 --emax 2 \
  --attempts 100000 --seconds 28800 --seed 202609231 \
  --out giraffes
