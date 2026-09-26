# Rank 100 discount sieve

Special-form trial factoring of `N = k*q + ε` **without building N**.
Does not call PFGW. Leave the Xeon walker (k=206) alone.

```
python3 ../rank100_discount.py --selftest
python3 ../rank100_discount.py --B 100000000 --max-k 400 --out .
python3 ../rank100_discount.py --B 1000000000 --max-k 400 --out .
```

`discount.jsonl` — every admissible k. `survivors.jsonl` — unkilled at this B.
Those survivors are the only k that should ever see a 25-hour Fermat.

First pass `B = 10^8`, `k = 98..400`: **9 survivors** (27 s on the Studio):

98, 100, 124, 142, 188, 206, 214, 230, 326.

k=98 and 100 have factors `1.63e8` and `3.93e8` (above this B). k=124, 142, 188 survived PFGW’s `1.66e9` then Fermat-composite. **k=206 is on the Xeon now — leave it.** 214, 230, 326 are the next Fermat-queue names after 206, unless a deeper `--B 1000000000` kills them.
