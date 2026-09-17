# Signed doors (spectral thread)

Sieve work parked. This note is covering-spectrum only.

## Rule (shared)
- Walk odd primes p ≤ N
- m = p − door, require |m| ≥ 2 and 3 ∤ |m|
- New prime factors of |m| join S
- 3 ∉ S ever

## Classic vs signed
- Classic doors: +1, +3
- Signed doors: +1, +3, −1, −3
- Cost: fewer missing, smaller sum, prefer |door|=3, then + over −

## Probe sizes (|S|)
| N | classic | signed | delta |
|---|---------|--------|-------|
| 100 | 9 | 4 | 5 |
| 500 | 27 | 13 | 14 |
| 2000 | 78 | 33 | 45 |
| 10000 | 272 | 109 | 163 |

Backward doors shrink the needed launcher spectrum substantially. −3 is heavily used.

Page: `/signed-doors`
