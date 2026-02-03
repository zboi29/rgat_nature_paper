# AGENTS.md — RGAT Nature Paper

## Project Summary
This repo contains the code and verification artifacts for the **Riemannian Geometric-Algebra Transformer (RGAT)** Nature paper. It formalizes that standard Transformer attention is a flat-geometry limit of a curved diffusion operator on the rotor manifold \(\Spin(3)\), and includes Lean 4 proofs plus Python validation/plotting.

## Source of Truth
- The LaTeX files in `docs/tex/` are the ground truth for formulas and definitions.
- When implementing or verifying code, cite the specific Equation or Theorem number from `docs/tex/si_rgat_nature.tex`.

## Key Theorems (Lean 4)
- **Lemma S1 (Sign Invariance):** `RgatNaturePaper.Geometry.Basic` (`sign_invariance`).
- **Lemma S2 (Small-angle expansion):** `RgatNaturePaper.Geometry.SmallAngle` (`LemmaS2`).
- **Theorem S4 (Bridge Theorem):**
  - Head-level: `RgatNaturePaper.Attention.Logits` (`bridge_theorem_head`).
  - Stack-level clause (explicit product of Lipschitz constants; assumes `Lip ≥ 1`): `RgatNaturePaper.Gradients.Proofs` (`BridgeTheoremStack`).
- **Theorem S13 (Depth Accumulation):** `RgatNaturePaper.Gradients.Proofs` (`TheoremS13`).

## Repository Layout
### Formal Verification (Lean 4)
- Root: `RgatNaturePaper/`
- Key files:
  - `RgatNaturePaper/Geometry/Basic.lean` — \(\Spin(3)\) rotors + geodesic distance (SI definitions).
  - `RgatNaturePaper/Geometry/SmallAngle.lean` — Lemma S2 small-angle expansion.
  - `RgatNaturePaper/Attention/Logits.lean` — logits + S4 head-level bridge.
  - `RgatNaturePaper/Gradients/Proofs.lean` — S3, S10–S14 proofs and stack-level bridge clause.

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
