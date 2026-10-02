# nm-notebook

The hire graph of the 3-free door. Alphabet toys and Lean live in the same repo.

Live site: [halfasecond.com](https://halfasecond.com)

## Hire graph

Lead shelf: the **hire graph of the 3-free door**.

- **Paper 1** — [*The hire graph of the 3-free door*](https://halfasecond.com/paper/hire-graph-of-the-3-free-door.pdf) ([TeX](paper/two_doors.tex)) · [note](https://halfasecond.com/notes/hire-graph)
- **Sequel** — [*When gold disconnects*](https://halfasecond.com/paper/when-gold-disconnects.pdf) ([TeX](paper/when_gold_disconnects.tex)) · [note](https://halfasecond.com/notes/when-gold-disconnects)
- **Zeta doors** — [*Prime neighbours of zeta denominators*](https://halfasecond.com/paper/zeta-doors.pdf) ([TeX](paper/zeta-doors.tex)) · [note](https://halfasecond.com/notes/zeta-doors)
- **Mid-gap / torus** — [*A midpoint identity for the complementary torus order at discriminant −3*](https://halfasecond.com/paper/mid-gap-and-torus.pdf) ([TeX](paper/mid-gap-and-torus.tex)) · [note](https://halfasecond.com/notes/mid-gap-and-torus)
- **Islands** — last-island / black-swan spotlight and the thin M₃₁ corridor · [site](https://halfasecond.com/islands)
- **Introduction / Basins** — door table and drain lattice · [hire](https://halfasecond.com/hire) · [basins](https://halfasecond.com/basins)
- **Hire lab** — rate, tail, mid-gap shelf · [hire-lab](https://halfasecond.com/hire-lab) · [torus](https://halfasecond.com/torus)

Paper 1 closes the question that every odd prime ≠ 3 eventually sits in the infinite gold component of 5 (Dirichlet bridge). The leftover is whether gold is disconnected for infinitely many finite windows — equivalent to infinitely many Mersenne or Fermat primes (*When gold disconnects*). The mid-gap note is Saturday Lab: elementary identity + frozen offset series; not an \(H(X)\) claim.

## Lean

Checked under `lean/Hire/` (build with `elan` / `lake`; Mathlib is not vendored). Spine is `lean/Hire.lean`.

- `Doors`, `HireSet`, `Graph`, `Finite` — 3-free door, hire set, star + gold; `mid_gap_m0`, `chi3_eq_legendreSym_neg_three`
- `StarLap`, `Lemma8`, `Cone` — Laplacian cone; `λ₂ = 1` iff gold-on-leaves is disconnected
- `WitnessXstar` — connecting witness at `X*`
- `GoldBridge` — strong Q2, 0 sorry: every odd prime ≠ 3 lies in the infinite gold component of 5
- `GoldDisconnects` — size bound, door closure, descent, sink reduction, window monotonicity, finite-set bridge, and arbitrarily large disconnected windows iff infinitely many prime 2-power doors
- `Dirichlet.lean` — Mathlib primes in AP wrapper; no sorry
- `TwoClassCoverage`, `InfiniteHire` — two hire classes modulo `6Q`, infinitely many prime owners of odd `Q` with `3 ∤ Q`, and `eventually_hired`
- `FLT` — checkpoint descents for exponents 3, 4, and 5; see `lean/Hire/FLT/README.md` for the proof map
- `FltTwoDoor.lean` — exploratory, not in the barrel

The cone bound `λ ≤ |V|` is the comparison with the complete graph. Same argument is proposed for Mathlib as [mathlib4#43953](https://github.com/leanprover-community/mathlib4/pull/43953); `Cone.lean` still carries a local copy until that lands. The gold-disconnects slice has no `sorry`, `admit`, or `axiom`.

## Run

```bash
npm install
npm run dev
```

```bash
npm run build
```

## Shelves

| Shelf | What |
|-------|------|
| **Hire** | Introduction, Basins, Islands, Corridor, Microscope, Certificates, Spectrum, Hire rate, notes |
| **Alphabet** | e, i, π — Walk, Lock i / π, Basel, Catalogue, Notes |
| **Toys** | Physics, Bell `(σ, p)`, switching atlas |
| **Lab** | More probes |

Certificates: owner-floor thin sieve at `B = 10⁷` across the PrimePages top 100 (99/100; skipped #82 primorial). Hunt closed; papers frozen. K_cert leaders #42 = 134, #75 = 116, #18 = 110.

## License

Apache-2.0 — see [`LICENSE`](LICENSE).
