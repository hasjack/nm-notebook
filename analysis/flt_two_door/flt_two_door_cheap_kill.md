# FLT × Hire two-door: cheap-kill experiment

Exploratory draft only. Papers frozen. Doors/hire voice only. No Mathlib PR / no push.

**Generated:** 2026-09-20 17:43 BST (Europe/London)  
**R (Germain):** 2,000,000  
**ℓ list:** [5, 7, 11, 13, 17, 19, 23, 29, 31]  
**Runtime:** 2.1s

## Room takeaway

### **KILL**

Door landing is exactly the elementary mod-3 split (ell|r-1 lands on m0 iff r%3=2, on m1 iff r%3=1). Motifs that recur are only the mod-3 door split plus generic 2-adic / cofactor noise; no finite forbidden door pattern forced by hypothetical FLT solutions appears.

Gold alone erases the FLT residue precisely when the auxiliary sits at `r ≡ 1 (mod 3)` (then `ℓ | m1`, so `ℓ` is not a gold factor of `m0`). That is the standing door definition, not a new obstruction.

## Door definitions (from `Hire/Doors.lean`)

- `chi3(n)`: +1 if n≡1 mod 3, −1 if n≡2, else 0
- `m0(p)` = 3-free door: `p+1` if `p%3==1` else `p−1`
- `m1(p)` = other face (div by 6): `p−1` if `p%3==1` else `p+1`
- Always `m0+m1=2p`; gold arcs use odd prime factors ≠3 of `m0`

## Elementary identity (DoorOfResidue)

If `ℓ ∣ (r−1)` and `r ≠ 3` is an odd prime, then by definition of `m0`/`m1`:

- `r ≡ 1 (mod 3)` ⇒ `m1(r) = r−1` ⇒ `ℓ ∣ m1` (and `ℓ ∤ m0`)
- `r ≡ 2 (mod 3)` ⇒ `m0(r) = r−1` ⇒ `ℓ ∣ m0` (and `ℓ ∤ m1`)

Verified computationally: identity_ok=123858, identity_bad=0, Germain mismatches=0, assert_failures=0.

## 1. Germain auxiliaries `r = 2kℓ+1 ≤ R`

| ℓ | total r | m0 | m1 | neither | r≡1 | r≡2 | m0∧r≡2 | m1∧r≡1 | mismatches | frac m0 |
|---:|--------:|---:|---:|--------:|----:|----:|-------:|-------:|-----------:|--------:|
| 5 | 37188 | 18648 | 18540 | 0 | 18540 | 18648 | 18648 | 18540 | 0 | 0.5015 |
| 7 | 24792 | 12414 | 12378 | 0 | 12378 | 12414 | 12414 | 12378 | 0 | 0.5007 |
| 11 | 14906 | 7474 | 7432 | 0 | 7432 | 7474 | 7474 | 7432 | 0 | 0.5014 |
| 13 | 12385 | 6192 | 6193 | 0 | 6193 | 6192 | 6192 | 6193 | 0 | 0.5 |
| 17 | 9299 | 4660 | 4639 | 0 | 4639 | 4660 | 4660 | 4639 | 0 | 0.5011 |
| 19 | 8231 | 4147 | 4084 | 0 | 4084 | 4147 | 4147 | 4084 | 0 | 0.5038 |
| 23 | 6773 | 3382 | 3391 | 0 | 3391 | 3382 | 3382 | 3391 | 0 | 0.4993 |
| 29 | 5360 | 2704 | 2656 | 0 | 2656 | 2704 | 2704 | 2656 | 0 | 0.5045 |
| 31 | 4924 | 2483 | 2441 | 0 | 2441 | 2483 | 2483 | 2441 | 0 | 0.5043 |

**Totals:** Germain hits=123858, m0=62104, m1=61754, mismatches=0.

Note: `r = 2kℓ+1` with `ℓ` odd ⇒ `r ≡ 1 (mod 2)`; mod-3 distribution of such primes is not forced 50/50 (depends on `2ℓ mod 3`), so m0/m1 counts need not be equal.

### v2 on the door that carries ℓ (Germain)

| door | v2 | count |
|------|---:|------:|
| m0 | 1 | 31053 |
| m0 | 2 | 15591 |
| m0 | 3 | 7767 |
| m0 | 4 | 3829 |
| m0 | 5 | 1911 |
| m0 | 6 | 967 |
| m0 | 7 | 495 |
| m0 | 8 | 240 |
| m0 | 9 | 126 |
| m0 | 10 | 61 |
| m0 | 11 | 34 |
| m0 | 12 | 9 |
| m0 | 13 | 16 |
| m0 | 14 | 1 |
| m0 | 15 | 4 |
| m1 | 1 | 30977 |
| m1 | 2 | 15534 |
| m1 | 3 | 7579 |
| m1 | 4 | 3814 |
| m1 | 5 | 1918 |
| m1 | 6 | 983 |
| m1 | 7 | 487 |
| m1 | 8 | 236 |
| m1 | 9 | 108 |
| m1 | 10 | 60 |
| m1 | 11 | 29 |
| m1 | 12 | 13 |
| m1 | 13 | 9 |
| m1 | 14 | 6 |
| m1 | 16 | 1 |

Cofactor=1 after stripping 2 and ℓ: m0→62, m1→0 (of 62104/61754).

## 2. Primitive-divisor proxy

Scan: a,b ∈ [1..12], gcd=1, N=a^ℓ+b^ℓ ≤ 1e+12, require ℓ∣(r−1) and r ∤ a^d+b^d for proper d∣ℓ.

| ℓ | total | m0 | m1 | match mod3 | mismatch |
|---:|------:|---:|---:|-----------:|---------:|
| 5 | 38 | 18 | 20 | 38 | 0 |
| 7 | 49 | 21 | 28 | 49 | 0 |
| 11 | 58 | 25 | 33 | 58 | 0 |
| 13 | 30 | 10 | 20 | 30 | 0 |
| 17 | 16 | 5 | 11 | 16 | 0 |
| 19 | 9 | 2 | 7 | 9 | 0 |
| 23 | 5 | 3 | 2 | 5 | 0 |
| 29 | 2 | 1 | 1 | 2 | 0 |
| 31 | 1 | 0 | 1 | 1 | 0 |

**Unique (ℓ,r) hits:** 208

## 3. Motif search

Top Germain motif keys (door, r%3, match_mod3, v2, cof1, gold_n):

```
 21241  ('door=m0', 'r%3=2', 'match_mod3=True', 'v2=1', 'cof1=False', 'gold_n=3')
 15076  ('door=m1', 'r%3=1', 'match_mod3=True', 'v2=1', 'cof1=False', 'gold_n=2')
 10358  ('door=m0', 'r%3=2', 'match_mod3=True', 'v2=2', 'cof1=False', 'gold_n=3')
  9805  ('door=m0', 'r%3=2', 'match_mod3=True', 'v2=1', 'cof1=False', 'gold_n=2')
  8695  ('door=m1', 'r%3=1', 'match_mod3=True', 'v2=1', 'cof1=False', 'gold_n=1')
  7263  ('door=m1', 'r%3=1', 'match_mod3=True', 'v2=2', 'cof1=False', 'gold_n=2')
  7197  ('door=m1', 'r%3=1', 'match_mod3=True', 'v2=1', 'cof1=False', 'gold_n=3')
  5224  ('door=m0', 'r%3=2', 'match_mod3=True', 'v2=2', 'cof1=False', 'gold_n=2')
  4887  ('door=m0', 'r%3=2', 'match_mod3=True', 'v2=3', 'cof1=False', 'gold_n=3')
  4425  ('door=m1', 'r%3=1', 'match_mod3=True', 'v2=2', 'cof1=False', 'gold_n=3')
  3846  ('door=m1', 'r%3=1', 'match_mod3=True', 'v2=2', 'cof1=False', 'gold_n=1')
  3538  ('door=m1', 'r%3=1', 'match_mod3=True', 'v2=3', 'cof1=False', 'gold_n=2')
  2876  ('door=m0', 'r%3=2', 'match_mod3=True', 'v2=3', 'cof1=False', 'gold_n=2')
  2276  ('door=m0', 'r%3=2', 'match_mod3=True', 'v2=4', 'cof1=False', 'gold_n=3')
  2132  ('door=m1', 'r%3=1', 'match_mod3=True', 'v2=3', 'cof1=False', 'gold_n=3')
  1909  ('door=m1', 'r%3=1', 'match_mod3=True', 'v2=3', 'cof1=False', 'gold_n=1')
  1796  ('door=m1', 'r%3=1', 'match_mod3=True', 'v2=4', 'cof1=False', 'gold_n=2')
  1546  ('door=m0', 'r%3=2', 'match_mod3=True', 'v2=4', 'cof1=False', 'gold_n=2')
  1067  ('door=m1', 'r%3=1', 'match_mod3=True', 'v2=4', 'cof1=False', 'gold_n=3')
  1041  ('door=m0', 'r%3=2', 'match_mod3=True', 'v2=5', 'cof1=False', 'gold_n=3')
```

No mismatch motifs. Every Germain and primdiv hit obeys the mod-3 door rule. Recurring structure is exactly that split; v2/cofactor variation looks generic (no fixed finite forbidden door graph across ℓ).

## 4. FLT contact reading

- Classical reduction: odd prime exponent ℓ; cyclotomic / Germain auxiliaries give primes r with ℓ∣(r−1).
- Hire gold uses odd prime factors ≠3 of **m0**. When the auxiliary has `r ≡ 1 (mod 3)`, ℓ lands on **m1** (sluice), so gold alone does not see the FLT residue — expected from door defs, not a new kill criterion beyond mod 3.
- When `r ≡ 2 (mod 3)`, ℓ lands on **m0** (gold-capable). That is again the definition, not an exotic motif.
- **Conclusion:** nothing computationally special beyond the expected mod-3 door split; no recurring exotic finite door pattern suggesting a forbidden configuration forced by hypothetical FLT solutions.

## Artifacts

- Script: `drafts/flt_two_door_cheap_kill.py`
- CSV (row-level): `drafts/flt_two_door_cheap_kill.csv`
- CSV (summary): `drafts/flt_two_door_cheap_kill_summary.csv`
- This report: `drafts/flt_two_door_cheap_kill.md`
- Lean stub (optional): `Hire/FltTwoDoor.lean`

## Paste-ready takeaway

**KILL.** Germain scan (R=2,000,000, ℓ∈[5, 7, 11, 13, 17, 19, 23, 29, 31]): 123858 auxiliaries, door landings m0=62104 / m1=61754, mismatches vs mod-3 rule = 0; primdiv proxy 208 hits, same exact split. Identity `ℓ∣r−1 ⇒ (ℓ∣m0 ↔ r≡2 mod 3)` holds with 123858 checks / 0 fails. Motifs that recur are only that split plus generic 2-adic/cofactor noise — no exotic finite door pattern. Gold erasing FLT residue at r≡1 mod 3 is definitional (ℓ on m1).
