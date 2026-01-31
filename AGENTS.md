# AGENTS.md — RGAT Nature Paper

## Project Summary
This repo contains the code and verification artifacts for the **Riemannian Geometric-Algebra Transformer (RGAT)** Nature paper. It formalizes that standard Transformer attention is a flat-geometry limit of a curved diffusion operator on the rotor manifold \(\Spin(3)\), and includes Lean 4 proofs plus Python validation/plotting.

## Source of Truth
- The LaTeX files in `docs/tex/` are the ground truth for formulas and definitions.
- When implementing or verifying code, cite the specific Equation or Theorem number from `docs/tex/si_rgat_nature.tex`.

## Key Theorems (Lean 4)
- **Theorem S4 (Bridge Theorem):** small-angle limit of geometric attention recovers dot-product attention. Lean: `RgatNaturePaper.BridgeTheorem`.
- **Lemma S1 (Sign Invariance):** geodesic distance is well-defined on the double cover \(\Spin(3) \to \SO(3)\).
- **Theorem S13 (Depth Accumulation):** depth accumulates curvature via BCH commutators, preventing deep Transformers from reducing to linear algebra.

## Repository Layout
### Formal Verification (Lean 4)
- Root: `RgatNaturePaper/`
- Key files:
  - `RgatNaturePaper/Basic.lean` — definitions of \(\Spin(3)\) rotors and geodesic distance (matches SI definitions).
  - `RgatNaturePaper/BridgeTheorem.lean` — main covariance proof.

### Validation & Visualization (Python)
- Root: `validation/`
- Key directories:
  - `validation/symbolic/` — SymPy scripts for specific lemmas (e.g., `validation_s1_sign_invariance.py` for Lemma S1).
  - `validation/plotting/` — scripts to reproduce Figure 1 (Conceptual Bridge) and Figure 2 (Empirical Validation).

## Environment Setup
### Python
- Create venv: `python3 -m venv .venv`
- Activate: `source .venv/bin/activate`
- Install deps: `pip install -r requirements.txt`
- Always activate `.venv` before running scripts in `validation/` or `scripts/`.

### Lean 4
- Build proofs: `lake build` (run from repo root).
- Edit: open `RgatNaturePaper/` in VS Code with the Lean 4 extension.

## Development Guidelines
- Always refer to the architecture as **Riemannian Geometric-Algebra Transformer (RGAT)**.
- Never use “Relational Graph Attention Networks” (deprecated terminology).

## Suggested Verification Workflow
1. Check math in `docs/tex/si_rgat_nature.tex`.
2. Run the corresponding script in `validation/symbolic/`.
3. Build the Lean project with `lake build`.
