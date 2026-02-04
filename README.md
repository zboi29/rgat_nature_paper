# RGAT: Riemannian Geometric-Algebra Transformers (Nature Paper)

[![DOI](https://zenodo.org/badge/1145602390.svg)](https://doi.org/10.5281/zenodo.18475945)
[![License: Apache-2.0](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](LICENSE)
[![Lean](https://img.shields.io/badge/Lean-4.24.0-5e6ad2.svg)](lean-toolchain)
[![Python](https://img.shields.io/badge/Python-3.10%2B-3776AB.svg)](requirements.txt)

This repository contains the official code and formal verification artifacts for the paper **"Riemannian Geometric-Algebra Transformers: A Curved-Geometry Limit of Standard Attention"**.

## Overview

This project presents a rigorous geometric interpretation of the Transformer architecture, linking **Spin(3)** geometry (rotors, quaternions), geodesic distances, and heat-kernel attention to Euclidean Gaussian kernels (the "Bridge Theorem").

The codebase adopts a hybrid approach:
*   **Formal Verification (Lean 4)**: Mathematical proofs of the core theorems, ensuring logical soundness.
*   **Symbolic Validation (Python)**: Symbolic checks and numeric experiments to validate the theoretical results and generate publication figures.

Formal verification, via Lean, now covers SI statements **S1–S14**, including the head‑level and stack‑level clauses of the Bridge Theorem.

## SI ↔ Lean Guide (For Editors and Reviewers)

If you are evaluating the scientific claims, start with:

- `docs/si_lean_guide.md` — direct mapping from SI statements to Lean files.
- `docs/review_path.md` — 5–10 minute verification path (statements → build).
- [docs/structure/dependency_graph.md](docs/structure/dependency_graph.md) — module dependency overview.
- [docs/structure/file_summaries.md](docs/structure/file_summaries.md) — per-file scope summaries.

These documents are written to make the proof layout auditable without prior Lean familiarity.

## Key Features

*   **Hybrid Verification**: Combines the strictness of interactive theorem proving (Lean 4) with the flexibility of symbolic computation (Python/SymPy).
*   **Bridge Theorem**: Explicitly maps the curved geometric operator to the flat Euclidean limit (head + stack).
*   **Reproducible Figures**: All figures in the paper can be regenerated from source using the provided scripts.
*   **Modular Lean layout**: Geometry, attention, gradients, and transformer statements are split into focused modules.

## Installation

### Prerequisites
*   **Python**: 3.10+
*   **Lean 4** (optional, for formal verification): See https://lean-lang.org/install/ for installation instructions.

### Lean Environment Details

*   **Lean toolchain**: `leanprover/lean4:v4.24.0` (see `lean-toolchain`)
*   **Mathlib**: `v4.24.0` (see `lakefile.toml`)
*   **Build entrypoint**: `RgatNaturePaper` (see `lakefile.toml`)

### Setup
1.  Clone the repository:
    ```bash
    git clone https://github.com/your-username/rgat_nature_paper.git
    cd rgat_nature_paper
    ```

2.  Install Python dependencies:
    ```bash
    python3 -m venv .venv
    source .venv/bin/activate
    pip install -r requirements.txt
    ```

## Quick Start
To immediately verify the "Bridge Theorem" visualization (Figure 1):

```bash
python3 validation/plotting/figure1_conceptual_bridge.py
```

For more validation details, see [validation/README.md](validation/README.md).

For Figure 2 and Figure 3 (Bridge Theorem scaling + empirical validation), run:

```bash
python3 validation/plotting/figure2_3_bridge_theorem.py
```

## Lean Quick Start (Non‑Lean Users)

From the repo root:

```bash
lake update
lake exe cache get
lake build
```
If you are offline or prefer a cold build, you can skip `lake exe cache get` (the build will be slower but correct).

## Repository Map (Lean)

```
RgatNaturePaper/
  Geometry/      # S1–S2 primitives and small-angle expansions
  Attention/     # Softmax/logits + S4–S8
  Transformers/  # S9 statement
  Gradients/     # S3, S10–S14 statements and proofs
```

See [docs/structure/dependency_graph.md](docs/structure/dependency_graph.md) and
[docs/structure/file_summaries.md](docs/structure/file_summaries.md) for a detailed dependency map.

## Reviewer Guide

For Nature editors, peer reviewers, and anyone interested in a deep dive into the scientific claims and their verification, please consult the **[Reviewers Guide](REVIEWERS.md)**.

The guide includes:
*   Detailed mapping between paper sections and code.
*   Step-by-step reproduction instructions for all figures.
*   A walkthrough of the Lean 4 formalization.
