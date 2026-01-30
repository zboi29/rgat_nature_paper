# Project: RGAT Nature Paper (Hybrid Lean 4 + Python)

## Overview
This repository contains the code and verification artifacts for the "RGAT" (Relational Graph Attention Networks) Nature paper. It is a hybrid project combining **Lean 4** for formal mathematical verification and **Python** for symbolic validation and visualization.

The core research focus is on the geometric interpretation of transformers, specifically linking **Spin(3)** geometry (rotors, quaternions), geodesic distances, and heat-kernel attention to Euclidean Gaussian kernels (the "Bridge Theorem").

## Architecture & Directory Structure

### 1. Formal Verification (Lean 4)
*   **Root:** `/`
*   **Main Library:** `RgatNaturePaper/`
*   **Build System:** `lake` (Lean 4)
*   **Status:** Early stage (scaffolding).
*   **Key Files:**
    *   `lakefile.toml`: Project configuration and dependencies (depends on `mathlib`).
    *   `RgatNaturePaper.lean`: Main library entry point.
    *   `RgatNaturePaper/Basic.lean`: Basic definitions.

### 2. Validation & Visualization (Python)
*   **Root:** `validation/`
*   **Purpose:** Symbolic checks of lemmas and generation of publication figures.
*   **Dependencies:** `sympy`, `numpy`, `matplotlib`, `torch`.
*   **Subdirectories:**
    *   `symbolic/`: Scripts checking mathematical properties (e.g., `validation_s1_sign_invariance.py` verifies Lemma S1).
    *   `plotting/`: Scripts generating figures (e.g., `plot_figure_1_conceptual_bridge.py`).

## Key Mathematical Concepts
*   **Spin(3) / S³:** The group of unit quaternions (rotors) representing 3D rotations.
*   **Geodesic Distance ($d_{geo}$):** Distance between rotations on the manifold.
*   **Heat Kernel:** Used for attention weights ($e^{-d_{geo}^2/2\tau}$).
*   **Bridge Theorem:** Establishes the connection between the curved geometric operator and the flat Euclidean limit (Transformer).

## Usage

### Building Lean Code
To build the Lean project:
```bash
lake build
```

### Running Validation Scripts
The Python scripts are standalone but may require a local module `gat_aimo3` (referenced in imports but possibly external or generated).

**Example: Symbolic Validation**
```bash
python3 validation/symbolic/validation_s1_sign_invariance.py
```

**Example: Plotting Figure 1**
```bash
python3 validation/plotting/plot_figure_1_conceptual_bridge.py
```

## Development Notes
*   **Source of Truth:** All mathematical definitions, theorems, and explanations must be referenced and cited from the TeX papers located in `docs/tex/` (specifically `rgat_nature.tex` and `si_rgat_nature.tex`). These files supersede any inline comments or code implementations.
*   **Conventions:**
    *   **Lean:** Follows standard Mathlib conventions.
    *   **Python:** Uses `argparse` for CLI, type hints, and structured validation steps.
*   **CI/CD:** GitHub Actions workflows in `.github/workflows/` handle CI (`lean_action_ci.yml`).
