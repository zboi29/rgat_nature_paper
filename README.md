# RGAT: Relational Graph Attention Networks (Nature Paper)

This repository contains the official code and formal verification artifacts for the paper **"Relational Graph Attention Networks"**.

## Overview

This project presents a rigorous geometric interpretation of the Transformer architecture, linking **Spin(3)** geometry (rotors, quaternions), geodesic distances, and heat-kernel attention to Euclidean Gaussian kernels (the "Bridge Theorem").

The codebase adopts a hybrid approach:
*   **Formal Verification (Lean 4)**: Mathematical proofs of the core theorems, ensuring logical soundness.
*   **Symbolic Validation (Python)**: Symbolic checks and numeric experiments to validate the theoretical results and generate publication figures.

## Key Features

*   **Hybrid Verification**: Combines the strictness of interactive theorem proving (Lean 4) with the flexibility of symbolic computation (Python/SymPy).
*   **Bridge Theorem**: Explicitly maps the curved geometric operator to the flat Euclidean limit.
*   **Reproducible Figures**: All figures in the paper can be regenerated from source using the provided scripts.

## Installation

### Prerequisites
*   **Python**: 3.10+
*   **Lean 4**: (Optional, for formal verification) Navigate to https://lean-lang.org/install/ for installation instructions.

### Setup
1.  Clone the repository:
    ```bash
    git clone https://github.com/your-username/rgat_nature_paper.git
    cd rgat_nature_paper
    ```

2.  Install Python dependencies:
    ```bash
    pip install -r requirements.txt
    ```

## Quick Start
To immediately verify the "Bridge Theorem" visualization (Figure 1):

```bash
python3 validation/plotting/plot_figure_1_conceptual_bridge.py
```

## Reviewer Guide

For Nature editors, peer reviewers, and anyone interested in a deep dive into the scientific claims and their verification, please consult the **[Reviewers Guide](REVIEWERS.md)**.

The guide includes:
*   Detailed mapping between paper sections and code.
*   Step-by-step reproduction instructions for all figures.
*   A walkthrough of the Lean 4 formalization.
