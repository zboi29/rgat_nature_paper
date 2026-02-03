# Reviewer's Guide

Welcome to the code repository for **"Riemannian Geometric-Algebra Transformers"**. This document is intended for editors, peer reviewers, and researchers who wish to verify the scientific claims, mathematical proofs, and experimental results presented in the paper.

## 1. Repository & Paper Mapping

The codebase is structured to mirror the paper's organization. The following table maps key sections of the paper to their corresponding code implementation and verification artifacts.

| Paper Section | Topic | Formal Verification (Lean 4) | Symbolic Validation (Python) |
| :--- | :--- | :--- | :--- |
| **Sec 2.1** | Spin(3) Attention | `RgatNaturePaper/Geometry/Basic.lean` | `validation/symbolic/validation_s1_sign_invariance.py` |
| **Sec 2.2** | The Bridge Theorem (Head) | `RgatNaturePaper/Attention/Logits.lean` | `validation/symbolic/validation_s4_bridge_theorem.py` |
| **Sec 3.1** | Stability / Softmax | `RgatNaturePaper/Attention/Softmax.lean` | `validation/symbolic/validation_s3_softmax_stability.py` |
| **Supp S1** | Sign Invariance | `RgatNaturePaper/Geometry/Basic.lean` | `validation/symbolic/validation_s1_sign_invariance.py` |
| **Supp S2** | Small Angle Approx | `RgatNaturePaper/Geometry/SmallAngle.lean` | `validation/symbolic/validation_s2_small_angle.py` |

## 2. Reproducing Figures

The figures in the paper are generated programmatically. You can reproduce them exactly using the scripts in `validation/plotting/`.

### Figure 1: The Geometric Bridge
Visualize the connection between heat diffusion on the manifold and the Gaussian kernel in tangent space.

```bash
python3 validation/plotting/plot_figure_1_conceptual_bridge.py
```
*   **Output**: A window displaying the interactive 3D comparison (or a saved file if run in headless mode).

### Figure 2 & 3: Bridge Theorem & Empirical Validation
Verify the $O(\epsilon^2)$ convergence rate and the error bounds.

```bash
python3 validation/plotting/plot_figure_2_bridge_theorem.py
```
*   **Output**: Generates the error analysis plots demonstrating the convergence rates predicted by the Bridge Theorem.

## 3. Symbolic Validation (Python)

We provide a suite of Python scripts that use `sympy` to symbolically check the mathematical properties derived in the Supplementary Information. These scripts act as an intermediate check between the paper's algebra and the formal Lean proofs.

To run a specific validation (e.g., verifying the sign invariance of the kernel):
```bash
python3 validation/symbolic/validation_s1_sign_invariance.py
```

To run all symbolic checks:
```bash
# Example: running all scripts in the directory
for script in validation/symbolic/*.py; do
    echo "Running $script..."
    python3 "$script"
done
```

**Key Validations:**
*   `validation_s4_bridge_theorem.py`: Symbolically expands the heat kernel to verify the Taylor series coefficients match the Euclidean Gaussian.
*   `validation_s9_gauge_equivariance.py`: Checks that the attention mechanism is independent of the choice of local coordinate frames.

## 4. Formal Verification (Lean 4)

The `RgatNaturePaper/` directory contains the Lean 4 source code.

### Reviewer Audit Checklist (5 steps)

1. **Confirm SI mapping.** Use `docs/si_lean_guide.md` to locate the statement you care about.
2. **Inspect the statement.** Open the referenced `Statements.lean` file and verify the Lean statement matches the SI wording (constants and hypotheses explicit).
3. **Inspect the proof.** Jump to the corresponding proof in `Proofs.lean` (or the module listed) and skim the structure; comments call out nontrivial steps.
4. **Run the checker.** Execute `lake build` to replay all proofs with the pinned toolchain.
5. **Cross‑reference equations.** When in doubt, compare against the exact equation or theorem number in `docs/tex/si_rgat_nature.tex`.

### Setup
Ensure you have Lean 4 installed (typically via `elan`).

### Verifying the Proofs
To compile the project and check all proofs:

```bash
lake build
```

If the command completes with no errors, all theorems in the library have been formally verified by the Lean kernel.

### Navigating the Proofs
*   **`RgatNaturePaper/Geometry/Basic.lean`**: Defines core Spin(3) geometry, geodesic distance, and sign invariance.
*   **`RgatNaturePaper/Attention/Logits.lean`**: Head‑level Bridge Theorem and logits/embedding machinery.
*   **`RgatNaturePaper/Attention/Softmax.lean`**: Softmax definitions and stability/derivative lemmas.
*   **`RgatNaturePaper/Gradients/Statements.lean`** and **`RgatNaturePaper/Gradients/Proofs.lean`**: S10–S14 statements and proofs (including stack‑level Bridge Theorem clause).

## 5. Directory Structure

```
.
├── RgatNaturePaper/       # Lean 4 Formal Verification
│   ├── Geometry/          # Spin(3) geometry + small‑angle lemmas (S1–S2)
│   ├── Attention/         # Softmax/logits + head‑level Bridge Theorem (S4)
│   ├── Transformers/      # Transformer statement (S9)
│   ├── Gradients/         # Gradient/curvature statements + proofs (S3, S10–S14)
│   └── ...
├── validation/            # Python Validation & Experiments
│   ├── plotting/          # Scripts to reproduce paper figures
│   └── symbolic/          # SymPy scripts checking lemmas
├── docs/                  # Documentation & LaTeX sources
├── lakefile.toml          # Lean build configuration
└── requirements.txt       # Python dependencies
```
