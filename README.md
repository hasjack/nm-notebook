# nm-notebook

The hire graph of the 3-free door. Alphabet toys and Lean live in the same repo.

## Hire graph

Lead shelf: the **hire graph of the 3-free door**.

- **Paper 1** — [*The hire graph of the 3-free door*](public/paper/hire-graph-of-the-3-free-door.pdf) ([TeX](paper/two_doors.tex)) · site: [`/notes/hire-graph`](/notes/hire-graph)
- **Sequel** — [*When gold disconnects*](public/paper/when-gold-disconnects.pdf) ([TeX](paper/when_gold_disconnects.tex)) · site: [`/notes/when-gold-disconnects`](/notes/when-gold-disconnects)
- **Zeta doors** — [*Prime neighbours of zeta denominators*](public/paper/zeta-doors.pdf) ([TeX](paper/zeta-doors.tex)) · site: [`/notes/zeta-doors`](/notes/zeta-doors) (Notes shelf, not Hire)
- **Islands** — last-island / black-swan spotlight and the thin M₃₁ corridor · site: [`/islands`](/islands)
- **Introduction / Basins** — door table and drain lattice · [`/hire`](/hire) · [`/basins`](/basins)

Paper 1 closes the question that every odd prime ≠ 3 eventually sits in the infinite gold component of 5 (Dirichlet bridge). The leftover is whether gold is disconnected for infinitely many finite windows — equivalent to infinitely many Mersenne or Fermat primes (*When gold disconnects*).

## Lean

Checked under `lean/Hire/` (build with `elan` / `lake`; Mathlib is not vendored). Spine is `lean/Hire.lean`.

- `Doors`, `HireSet`, `Graph`, `Finite` — 3-free door, hire set, star + gold
- `StarLap`, `Lemma8`, `Cone` — Laplacian cone; `λ₂ = 1` iff gold-on-leaves is disconnected
- `WitnessXstar` — connecting witness at `X*`
- `GoldBridge` — strong Q2, 0 sorry: every odd prime ≠ 3 lies in the infinite gold component of 5
- `GoldDisconnects` — sequel A (first-owner isolation + sink chains)
- `Dirichlet.lean` — still a stub (`eventually_hired`)
- `FltTwoDoor.lean` — exploratory, not in the barrel

The cone bound `λ ≤ |V|` is the comparison with the complete graph. Same argument is proposed for Mathlib as [mathlib4#43953](https://github.com/leanprover-community/mathlib4/pull/43953); `Cone.lean` still carries a local copy until that lands.

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
