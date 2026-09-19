# Natural Mathematics — nm-notebook

Open notebook for Natural Mathematics: explore on the web, or publish lemmas with Lean proofs.

## Hire graph

Lead shelf: the **hire graph of the 3-free door**.

- **Paper 1** — [*The hire graph of the 3-free door*](public/paper/hire-graph-of-the-3-free-door.pdf) ([TeX](paper/two_doors.tex)) · site: [`/paper`](http://127.0.0.1:5173/paper)
- **Sequel** — [*When gold disconnects*](public/paper/when-gold-disconnects.pdf) ([TeX](paper/when_gold_disconnects.tex)) · site: [`/when-gold-disconnects`](http://127.0.0.1:5173/when-gold-disconnects)
- **Islands** — last-island / black-swan spotlight and the thin M₃₁ corridor · site: [`/islands`](http://127.0.0.1:5173/islands)
- **Introduction / Basins** — door table and drain lattice · [`/hire`](http://127.0.0.1:5173/hire) · [`/basins`](http://127.0.0.1:5173/basins)

Paper 1 closes the question that every odd prime ≠ 3 eventually sits in the infinite gold component of 5 (Dirichlet bridge). The leftover is whether gold is disconnected for infinitely many finite windows — equivalent to infinitely many Mersenne or Fermat primes (*When gold disconnects*).

## Lean

Checked under `lean/Hire/` (build with `elan` / `lake`; Mathlib is not vendored):

- `Doors`, `HireSet`
- `WitnessXstar` — connecting witness at X*
- `GoldBridge` — strong Q2 (0 sorry)
- `GoldDisconnects` — sequel A (first-owner disconnect + sink chains)


## Run

```bash
npm install
npm run dev
```

Open http://127.0.0.1:5173/ — or `docker compose up` on the Mac.

```bash
npm run build
```

## Shelves

| Shelf | What |
|-------|------|
| **Hire** | Papers, Islands, Basins, Introduction |
| **Alphabet** | e, i, π — Walk, Lock i / π, Basel, Catalogue, Notes |
| **Lab** | Probe pages |

## License

Apache-2.0 (see Lean file headers). Add a root `LICENSE` if you cut a public release tag.
