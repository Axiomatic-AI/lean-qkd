# Quantum Key Distribution: High Fidelity Implies Low Entropy

Lean 4 formalization of Lemma 1 from [*Unconditional Security Of Quantum Key Distribution Over Arbitrarily Long Distances*](https://arxiv.org/abs/quant-ph/9802025) by Lo and Chau (1998).

## Main Theorem

If a density matrix ρ has high fidelity (> 1-δ) with a pure state, then its von Neumann entropy is bounded:

```lean
S(ρ) ≤ -(1-δ) log(1-δ) - δ log(δ/(R-1))
```

## Building the Project

```bash
lake update
lake exe cache get
lake build
```

## Blueprint Documentation

Install and set up leanblueprint. **Note:** leanblueprint requires graphviz to be installed first. See the [leanblueprint documentation](https://github.com/PatrickMassot/leanblueprint) for system requirements before proceeding.

```bash
pip install leanblueprint
```

### Useful Commands

Build and serve the blueprint locally:
```bash
leanblueprint web
leanblueprint serve
```
Then visit `http://0.0.0.0:8000/` in your browser.

Build the PDF version:
```bash
leanblueprint pdf
```

## License

This project is licensed under the MIT License - see the [LICENSE](LICENSE) file for details.
