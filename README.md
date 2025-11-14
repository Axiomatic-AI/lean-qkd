# Quantum Key Distribution: High Fidelity Implies Low Entropy

**Authors:** Ben Breen & Kfir Sulimany

Lean 4 formalization of Lemma 1 from [*Unconditional Security Of Quantum Key Distribution Over Arbitrarily Long Distances*](https://arxiv.org/abs/quant-ph/9802025) by Lo and Chau (1998).

**Blueprint:** [BenKBreen.github.io/QKD](https://BenKBreen.github.io/QKD)

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

**Prerequisites:**
- Python ≥ 3.7
- Graphviz:
  - macOS: `brew install graphviz`
  - Linux: `sudo apt-get install graphviz graphviz-dev`

**Setup:**

1. Install leanblueprint:
   ```bash
   pip install leanblueprint
   ```

2. If installation fails with `pygraphviz` errors on macOS:
   ```bash
   pip install --config-settings="--global-option=build_ext" \
     --config-settings="--global-option=-I$(brew --prefix graphviz)/include" \
     --config-settings="--global-option=-L$(brew --prefix graphviz)/lib" \
     pygraphviz
   pip install leanblueprint
   ```

3. Generate the blueprint:
   ```bash
   cd blueprint
   leanblueprint web
   ```

The blueprint will be at `blueprint/web/index.html`.

## License

This project is licensed under the MIT License - see the [LICENSE](LICENSE) file for details.
