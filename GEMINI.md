# Project: RGAT Nature Paper (Hybrid Lean 4 + Python)

## Formalism & Theory
This repository contains the code and verification artifacts for the **Riemannian Geometric-Algebra Transformer (RGAT)** Nature paper. The project rigorously establishes that standard Transformer attention is a flat-geometry limit of a curved diffusion operator on the rotor manifold $\Spin(3)$.

### Core Thesis
As detailed in **@[docs/tex/rgat_nature.tex]**, the central discovery is that the attention mechanism arises from Heat Kernel diffusion on the Lie group $\Spin(3)$:
$$ K(\mu_i, r_j) = \exp\left(-\frac{d_{\mathrm{geo}}(\mu_i, r_j)^2}{2\tau}\right) $$
where $d_{\mathrm{geo}}$ is the intrinsic geodesic distance on the manifold.

### Key Theorems (Formalized)
The following theorems from **@[docs/tex/si_rgat_nature.tex]** are the mathematical backbone of this project and are verified in Lean 4:

*   **Theorem S4 (The Bridge Theorem)**: Proves that in the small-angle limit ($\varepsilon \to 0$), the geometric attention weights converge to the Euclidean Dot-Product Self-Attention of standard Transformers.
    *   *Lean formalism*: `RgatNaturePaper.BridgeTheorem`
*   **Lemma S1 (Sign Invariance)**: Establishes that the geodesic distance is well-defined on the double cover $\Spin(3) \to \SO(3)$.
*   **Theorem S13 (Depth Accumulation)**: Shows that even with near-Euclidean layers, depth accumulates curvature via Baker-Campbell-Hausdorff commutators, preventing deep Transformers from being reducible to linear algebra.

## Architecture & Directory Structure

### 1. Formal Verification (Lean 4)
*   **Root:** `RgatNaturePaper/`
*   **Goal:** Machine-checkable proofs of Theorems S4, S13, and related lemmas.
*   **Key Files:**
    *   `RgatNaturePaper/Basic.lean`: Definitions of $\Spin(3)$ rotors and geodesic distance (matches **SI Definitions**).
    *   `RgatNaturePaper/BridgeTheorem.lean`: The main covariance proof.

### 2. Validation & Visualization (Python)
*   **Root:** `validation/`
*   **Goal:** Symbolic validation of algebraic steps and generation of paper figures.
*   **Key Directories:**
    *   `validation/symbolic/`: SymPy scripts checking specific lemmas (e.g., `validation_s1_sign_invariance.py` checks **Lemma S1**).
    *   `validation/plotting/`: Scripts to reproduce **Figure 1** (Conceptual Bridge) and **Figure 2** (Empirical Validation).

## Environment & Management

### Python Environment
We use a standard virtual environment (`.venv`) to manage Python dependencies.
1.  **Creation**: `python3 -m venv .venv`
2.  **Activation**: `source .venv/bin/activate`
3.  **Dependencies**: Install via `pip install -r requirements.txt`

Always ensure the virtual environment is active before running any scripts in `validation/` or `scripts/`.

### Lean 4 Management
The formal verification component is managed by `lake` (Lean Make).
1.  **Build**: Run `lake build` from the repository root to compile the proofs.
2.  **Edit**: Open the `RgatNaturePaper/` directory in VS Code with the Lean 4 extension enabled.

## Development Guidelines

### Terminology
*   **ALWAYS** refer to the architecture as **Riemannian Geometric-Algebra Transformer (RGAT)**.
*   **NEVER** use "Relational Graph Attention Networks" (deprecated terminology).

### Source of Truth
*   The LaTeX files in **@[docs/tex/]** are the ground truth for all formulas and definitions.
*   When implementing or verifying code, cite the specific Equation or Theorem number from `docs/tex/si_rgat_nature.tex`.

### Verification Workflow
1.  **Check the Math**: Refer to definitions in `docs/tex/si_rgat_nature.tex`.
2.  **Run Symbolic Check**: execute the corresponding script in `validation/symbolic/`.
3.  **Run Formal Proof**: Build the Lean project with `lake build`.
