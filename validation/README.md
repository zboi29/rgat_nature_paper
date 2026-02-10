# Validation & Verification Guide

This directory contains the Python scripts used to validate the mathematical claims of the RGAT paper and reproduce its figures. The validation is split into two categories: **Symbolic Verification** (algebraic checks) and **Plotting** (empirical figures).

## Directory Structure

*   `symbolic/`: SymPy scripts that check SI lemmas/theorems (S1–S14).
*   `plotting/`: Figure-generation scripts for the main paper and SI.

## 1. Symbolic Verification (`validation/symbolic/`)

These scripts use Python's symbolic mathematics library, `sympy`, to verify lemmas and theorems from **@[docs/tex/si_rgat_paper.tex]**. They serve as an intermediate check between the paper's derivations and the full formalization in Lean 4.

Note: not every SI statement has a symbolic script; the table below reflects what is implemented.

### Key Scripts vs. SI Statements

| Script | Paper Section (SI) | Description |
| :--- | :--- | :--- |
| `validation_s1_sign_invariance.py` | **Lemma S1** | Verifies that geodesic distance is invariant to rotor sign ($q \to -q$). |
| `validation_s2_small_angle.py` | **Lemma S2** | Checks the Taylor expansion of geodesic distance in the small-angle regime. |
| `validation_s3_softmax_stability.py` | **Lemma S3** | Verifies the Lipschitz stability of the softmax function. |
| `validation_s4_bridge_theorem.py` | **Theorem S4** | The **core validation**: Expands the geometric heat kernel to show it matches the Euclidean Gaussian kernel to $O(\varepsilon^2)$. |
| `validation_s5_markov_diffusion.py` | **Theorem S5** | Checks row-stochasticity and diffusion interpretation. |
| `validation_s7_s8_truncation.py` | **Corollaries S7–S8** | Verifies truncation identities and bounds. |
| `validation_s9_gauge_equivariance.py` | **Theorem S9** | Checks that attention weights are invariant to global manifold rotations. |
| `validation_s10_geodesic_gradient.py` | **Theorem S10** | Verifies the geodesic alignment gradient on $S^3$. |
| `validation_s12_bch_accumulation.py` | **Lemma S12** | Checks BCH accumulation of small rotations. |
| `validation_s13_depth_curvature.py` | **Theorem S13** | Checks depth-accumulated curvature terms. |
| `validation_s14_rotor_flow_approx.py` | **Corollary S14** | Validates stack-level rotor-flow approximation. |

### Usage
Run any script directly with Python:
```bash
python3 validation/symbolic/validation_s1_sign_invariance.py
```
A successful run will print "PASS" or "Verification Successful" along with the symbolic steps checked.

## 2. Empirical Validation & Plotting (`validation/plotting/`)

These scripts reproduce the figures from the main manuscript, demonstrating the geometric bridge and its empirical scaling properties.

### Figure 1: The Conceptual Bridge
**Script:** `figure1_conceptual_bridge.py`
**Goal:** Visualize how heat diffusion on the sphere (curved geometry) becomes a Gaussian kernel in the tangent plane (flat geometry). The script produces a single figure with a main panel and an inset.
```bash
python3 validation/plotting/figure1_conceptual_bridge.py
```

### Figure 2 & 3: Bridge Theorem Scaling + Empirical Validation
**Script:** `figure2_3_bridge_theorem.py`
**Goal:** Empirically verify the $O(\varepsilon^2)$ convergence rate predicted by Theorem S4 and the linear depth scaling from Corollary S14.
```bash
python3 validation/plotting/figure2_3_bridge_theorem.py
```
*   **Figure 2**: Log-log plot of attention error vs. angle $\varepsilon$. Slope $\approx 2.0$.
*   **Figure 3**: Error accumulation with depth $L$. Trends purely linearly.

## Source of Truth
All validation targets are defined formally in:
*   **Definitions & Proofs**: `docs/tex/si_rgat_paper.tex`
*   **Main Thesis**: `docs/tex/rgat_paper.tex`

Please refer to these files for the exact mathematical statements being tested.
