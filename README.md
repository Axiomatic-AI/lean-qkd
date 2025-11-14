# QKD Formalization Project

Formalization of Peter Shor's certificate theorem for quantum key distribution in Lean 4.

## Project Structure

```
QKD/
├── QKD/
│   └── PeterShor.lean      # Main formalization file
├── lakefile.lean            # Lake build configuration
├── lean-toolchain           # Lean version specification
└── README.md               # This file
```

## Main Results

This project formalizes:

1. **Schur Convexity**: The function `f(x) = ∑ᵢ xᵢ log(xᵢ)` is Schur-convex
2. **High Fidelity Implies Low Entropy**: For a positive semidefinite density matrix ρ with trace 1, if there exists a unit vector achieving fidelity > 1-δ, then the von Neumann entropy is bounded

### Key Theorem

```lean
theorem high_fidelity_implies_low_entropy_equivalent
    (R : ℕ)
    (δ : ℝ)
    (ρ : Matrix (Fin R) (Fin R) ℂ)
    (hR : 1 < R)
    (hδ_pos : 0 ≤ δ)
    (hδ_lt_one : δ < 1)
    (hδ_small : δ ≤ (R - 1 : ℝ) / R)
    (hρ_pos : ρ.PosSemidef)
    (trace_one : ∑ i, hρ_pos.isHermitian.eigenvalues i = 1)
    (hv : ∃ v : EuclideanSpace ℂ (Fin R), norm v = 1 ∧ (⟪v, ρ *ᵥ v⟫_ℂ).re > 1 - δ)
    :
    (vonNeumannEntropy ρ).re ≤ -(1 - δ) * Real.log (1 - δ) - δ * Real.log (δ / (R - 1))
```

## Building the Project

### Prerequisites

- Lean 4.25.0-rc2
- Lake (comes with Lean)

### Installation

1. Install [elan](https://github.com/leanprover/elan):
   ```bash
   curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
   ```

2. Clone this repository:
   ```bash
   git clone <repository-url>
   cd QKD
   ```

3. Build the project:
   ```bash
   lake update
   lake exe cache get  # Download mathlib cache
   lake build
   ```

### Working with the Code

To work on the formalization:

```bash
# Open in VS Code with Lean extension
code .

# Or build specific files
lake build QKD.PeterShor
```

## Key Definitions

- **`vonNeumannEntropy`**: Von Neumann entropy S(ρ) = -tr(ρ log ρ)
- **`SchurConvex`**: A function is Schur-convex if it preserves the majorization ordering
- **`slope_comparison_tlogt`**: Key lemma showing t log t is a convex function

## Dependencies

- **Mathlib**: Lean's mathematical library
- Matrix theory, linear algebra, analysis
- Order theory (for Schur convexity)

## References

This formalization is based on Peter Shor's work on quantum key distribution security proofs.

## License

[Add appropriate license]

## Contributing

Contributions are welcome! Please feel free to submit pull requests or open issues.

