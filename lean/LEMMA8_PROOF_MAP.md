# Lemma 8 — proof map

Target claim (note, cone formula): on the hire graph \(H_X\) (star on 2 plus undirected gold),
\(\lambda_2(H_X)=1\) exactly when the undirected gold graph on the leaves is disconnected
(\(\mu_2(L'_X)=0\)).

```
Paper path
──────────
Lemma 7   λ_max(H_X)=n   (star eigenvector; gold edges contribute 0)
    │
    ▼
Lemma 8   cone / block form
          H_X = [ k  -1ᵀ ]
                [ -1  I+L' ]
          ⇒  spec(H_X) = {0,n} ∪ {1+μ₂,…,1+μ_{n-1}}
          ⇒  λ₂(H_X)=1  ⟺  gold-on-leaves disconnected
```

```
Lean path today (lean/Hire/)
───────────────────────────
Doors / HireSet / Graph / StarLap
    │
    ▼
GoldFree  ──►  G = Gstar  ──►  1 ∈ spectrum, n ∈ spectrum, Connected
               (Lemma8.lean forward)         (StarLap helpers)

lemma8_converse_sketch : HasSecondLaplacianEigenvalueOne ⇒ GoldFree
    └── sorry   (needs Laplacian interlacing / edge monotonicity)

GoldLeavesDisconnected  := ¬ (GgoldLeaves).Connected
    └── distinct from GoldFree; forests allowed
    └── GoldFree ⇒ GoldLeavesDisconnected (when ≥2 leaves)
    └── money line / μ₂(L')=0 is Layer D, needs cone formula
```

## Layers

| Layer | Content | Status |
|-------|---------|--------|
| A | `GoldFree` ⇒ `G = Gstar` ⇒ `1` and `n` in spectrum | Checked (`Lemma8` + `StarLap`) |
| B | Converse at zero-gold: spectral ⇒ `GoldFree` | Open (`sorry`; interlacing) |
| C | Cone formula `spec(H_X) = {0,n} ∪ {1+μ_i}` | Paper-only |
| D | Money line: `λ₂=1` ⟺ `GoldLeavesDisconnected` (forests allowed) | Paper-only; needs C + leaf gold connectivity |

## Dependency order for Lean

1. Keep Layer A as the present stake.
2. Layer B: Mathlib Laplacian edge-monotonicity / Cauchy interlacing relative to the star.
3. Layer C: block Laplacian / quotient by the all-ones leaf subspace (cone formula).
4. Layer D: transport Layer C through `GoldLeavesDisconnected` (`¬ (GgoldLeaves).Connected` / `μ₂(L')=0`).

Layer B alone does not unlock Layer D: zero gold is stricter than a disconnected forest.

## Modules

- Checked spine: `Doors`, `HireSet`, `Graph`, `StarLap`, `Lemma8` forward
- Named separately: `HireLeaf`, `GgoldLeaves`, `GoldLeavesDisconnected` (no longer an alias of `GoldFree`)
- Open: `Lemma8` converse `sorry`; Dirichlet owner stub in `Dirichlet.lean`
- Paper: `paper/two_doors.tex` Lemmas 7–8 and the window table
