# Quantum Key Distribution: High Fidelity Implies Low Entropy

**Authors:** Ben Breen & Kfir Sulimany

Lean 4 formalization of Lemma 1 from [*Unconditional Security Of Quantum Key Distribution Over Arbitrarily Long Distances*](https://arxiv.org/abs/quant-ph/9802025) by Lo and Chau (1998).

**Blueprint:** [BenKBreen.github.io/QKD](https://BenKBreen.github.io/QKD)

## Main Theorem

If a density matrix ρ has high fidelity (> 1-δ) with a pure state, then its von Neumann entropy is bounded:

```lean
S(ρ) ≤ -(1-δ) log(1-δ) - δ log(δ/(R-1))
```

## Building

```bash
lake update
lake exe cache get
lake build
```

## Blueprint

Generate the documentation:

```bash
cd blueprint
leanblueprint web
open web/index.html
```

