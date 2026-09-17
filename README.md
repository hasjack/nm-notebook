# e-walk-app

Jack’s local explorer for a number line spoken only in **e**, **i**, and **π**.

Envisage base^(iπ) when the base is free. Then lock i and watch π; lock π and watch i. Exploring, not claiming breakthroughs.

Landing on −1 (with one factor held at 1) means the free factor times ln(base) is an odd integer.

## Run

```bash
npm install
npm run dev
```

Then open http://127.0.0.1:5173/.

## Routes

| Path | View |
|------|------|
| `/` | **Walk** — variable base (ln slider), classical iπ (α=β=1) |
| `/lock-i` | **Lock i** — α=1; retune π-factor β (or free-β) |
| `/lock-pi` | **Lock π** — β=1; retune i-factor α (or free-α) |
| `/solve` | **Solve** — odd + free factor → base = e^(odd/factor) |
| `/notes` | **Notes** — benefits in e/i/π language |

Legacy `/lock` redirects to `/lock-i`; `/split` redirects to `/`.

## Maths

Helpers in `src/lib/walk.ts`: `curve`, `resultAt`, `walk`, `piFactorForMinusOne`, `iFactorForMinusOne`, `baseForMinusOne`. UI says i-factor / π-factor / base — never **k**.

## Build

```bash
npm run build
```

## Formal (Lean)

Companion proofs for the **3-free door** / hire graph live in [`lean/`](lean/). Checked with Lean 4 + Mathlib (`lake build` inside `lean/`). Sources ship with the site for GitHub Pages; the `.lake` cache is gitignored.

See [`lean/README.md`](lean/README.md).
