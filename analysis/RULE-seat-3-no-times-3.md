# Super primes — formal rule (seat 3, no ×3)

## Rule
1. Walk odd primes `p ≤ N` in order.
2. Write `p = m + d` with `d ∈ {1, 3}`. Prefer `d = 3`.
3. **`m` must be 3-free** (`3 ∤ m`). The integer 3 appears only as the additive seat `+3`, never as a multiplicative factor.
   - For every prime `p > 3`, `p − 3` is automatically 3-free.
   - Keep `d = 1` only when `3 ∤ (p − 1)` and that door is cheaper.
4. Seed: `3 = 2 + 1` (starts `S` with `{2}`).
5. Every prime factor of `m` not already in `S` is added to `S` — a **super prime** (launcher).
6. **3 is never in `S`** and never launches a spiral.

## Examples
- `7 = 2·2 + 3`
- `23 = 2·2·5 + 3`
- `79 = 2·2·19 + 3` (not `2·3·13 + 1`)
- `439 = 2·2·109 + 3` (not `2·3·73 + 1`)

## Meaning
- **Super primes** = orange launchers (braids of multiples).
- **Passengers** = other odd primes (including 3) that ride existing braids.
