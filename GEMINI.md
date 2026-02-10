# Project: RGAT Paper Proofs (Hybrid Lean 4 + Python)

## Formalism & Theory
This repository contains the code and verification artifacts for the **Riemannian Geometric-Algebra Transformer (RGAT)** paper. The project rigorously establishes that standard Transformer attention is a flat-geometry limit of a curved diffusion operator on the rotor manifold $\Spin(3)$.

### Core Thesis
As detailed in **@[docs/tex/rgat_paper.tex]**, the central discovery is that the attention mechanism arises from Heat Kernel diffusion on the Lie group $\Spin(3)$:
$$ K(\mu_i, r_j) = \exp\left(-\frac{d_{\mathrm{geo}}(\mu_i, r_j)^2}{2\tau}\right) $$
where $d_{\mathrm{geo}}$ is the intrinsic geodesic distance on the manifold.

### Key Theorems (Formalized)
The following theorems from **@[docs/tex/si_rgat_paper.tex]** are the mathematical backbone of this project and are verified in Lean 4 (S1–S14):

*   **Lemma S1 (Sign Invariance)**: `RgatPaperProofs.Geometry.Basic` (`sign_invariance`).
*   **Lemma S2 (Small-angle expansion)**: `RgatPaperProofs.Geometry.SmallAngle` (`LemmaS2`).
*   **Theorem S4 (The Bridge Theorem)**:
    *   Head-level: `RgatPaperProofs.Attention.Logits` (`bridge_theorem_head`)
    *   Stack-level clause (explicit product of Lipschitz constants; assumes `Lip ≥ 1`): `RgatPaperProofs.Gradients.Proofs` (`BridgeTheoremStack`)
*   **Theorem S13 (Depth Accumulation)**: `RgatPaperProofs.Gradients.Proofs` (`TheoremS13`)

For a complete SI statement index and file map, see `docs/si_lean_guide.md`.

## Architecture & Directory Structure

### 1. Formal Verification (Lean 4)
*   **Root:** `RgatPaperProofs/`
*   **Goal:** Machine-checkable proofs of Theorems S1–S14 and supporting lemmas.
*   **Key Files:**
    *   `RgatPaperProofs/Geometry/Basic.lean`: Definitions of $\Spin(3)$ rotors and geodesic distance (SI definitions).
    *   `RgatPaperProofs/Geometry/SmallAngle.lean`: Small-angle expansion (Lemma S2).
    *   `RgatPaperProofs/Attention/Logits.lean`: Logits and head-level Bridge Theorem (S4).
    *   `RgatPaperProofs/Gradients/Proofs.lean`: Gradient proofs, stack-level bridge clause, and S13/S14 machinery.

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
2.  **Edit**: Open the `RgatPaperProofs/` directory in VS Code with the Lean 4 extension enabled.

## Development Guidelines

### Terminology
*   **ALWAYS** refer to the architecture as **Riemannian Geometric-Algebra Transformer (RGAT)**.
*   **NEVER** use "Relational Graph Attention Networks" (deprecated terminology).

### Source of Truth
*   The LaTeX files in **@[docs/tex/]** are the ground truth for all formulas and definitions.
*   When implementing or verifying code, cite the specific Equation or Theorem number from `docs/tex/si_rgat_paper.tex`.

### Verification Workflow
1.  **Check the Math**: Refer to definitions in `docs/tex/si_rgat_paper.tex`.
2.  **Run Symbolic Check**: execute the corresponding script in `validation/symbolic/`.
3.  **Run Formal Proof**: Build the Lean project with `lake build`.
