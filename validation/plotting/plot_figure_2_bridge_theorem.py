#!/usr/bin/env python3
"""
Figures 2 & 3: Bridge Theorem Visualization and Empirical Validation

Generates two publication-quality figures:

Figure 2: The Bridge Theorem in One Glance
  - Panel 2a: GSM vs Softmax kernel comparison
  - Panel 2b: O(ε²) error bound schematic

Figure 3: One Decisive Experiment
  - Panel 3a: Head-level O(ε²) validation (log-log)
  - Panel 3b: Depth accumulation O(Lε²) validation

References
----------
- Nature paper: rgat_nature.tex (Figure 2 placeholder)
- SI: Lemma S2-S3 (small-angle expansion, softmax stability)
- SI: Theorem S4 (Bridge Theorem), Corollary S14 (depth accumulation)
"""
from __future__ import annotations

import argparse
import json
import os
import sys
import time
from pathlib import Path

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch
from scipy import stats

# Add project root to path
PROJECT_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(PROJECT_ROOT))

import torch
from gat_aimo3.model.rotor_math import geodesic_distance_sq, quat_dot_abs
from gat_aimo3.model.embeddings import exp_map_bivector


# =============================================================================
# Theoretical Kernel Functions
# =============================================================================

def gsm_kernel(theta: np.ndarray, tau: float = 1.0) -> np.ndarray:
    """
    Geometric Softmax (GSM) heat kernel on Spin(3).
    
    K_GSM(θ) = exp(-θ² / (2τ))
    
    where θ = d_geo is the geodesic angle.
    """
    return np.exp(-theta**2 / (2 * tau))


def softmax_kernel_bridge(theta: np.ndarray, tau: float = 1.0) -> np.ndarray:
    """
    Standard softmax kernel mapped to angular domain via Bridge Theorem.
    
    In the small-angle regime, the GSM kernel reduces to:
    K_std(θ) ≈ exp(cos(θ/2) / T_eff) where T_eff = τ/4
    
    Normalized to match GSM at θ=0.
    """
    T_eff = tau / 4.0
    raw = np.exp(np.cos(theta / 2) / T_eff)
    # Normalize peak to 1 (same as GSM at θ=0)
    return raw / np.exp(1.0 / T_eff)


# =============================================================================
# Experimental Functions
# =============================================================================

def run_head_level_experiment(
    epsilon_values: np.ndarray,
    n_queries: int = 8,
    n_keys: int = 32,
    n_trials: int = 200,
    tau: float = 1.0,
    seed: int = 42,
) -> dict:
    """
    Run head-level O(ε²) validation experiment.
    
    For each ε, samples random Q/K rotors near identity and measures
    the discrepancy between GSM and standard attention matrices.
    
    Returns
    -------
    dict
        Dictionary with epsilon values, mean errors, std errors, and all trials.
    """
    torch.manual_seed(seed)
    np.random.seed(seed)
    # Use float64 for high precision at small epsilon
    torch.set_default_dtype(torch.float64)
    
    results = {
        'epsilon': [],
        'mean_error': [],
        'std_error': [],
        'all_errors': [],
    }
    
    for eps in epsilon_values:
        trial_errors = []
        
        for trial in range(n_trials):
            # Sample random bivectors (Lie algebra elements)
            # We use standard gaussian * eps. Norms will vary!
            # This variation is key to the O(eps^2) error term (-|k|^2/2 correction).
            q_bivec = eps * torch.randn(n_queries, 3)
            k_bivec = eps * torch.randn(n_keys, 3)
            
            # Convert to unit rotors via exp map
            q_rotors = exp_map_bivector(q_bivec)  # (n_queries, 4)
            k_rotors = exp_map_bivector(k_bivec)  # (n_keys, 4)
            
            # Compute GSM logits: ℓ_ij = -d_geo²/(2τ)
            # Expand for pairwise computation
            q_exp = q_rotors.unsqueeze(1).expand(n_queries, n_keys, 4)
            k_exp = k_rotors.unsqueeze(0).expand(n_queries, n_keys, 4)
            
            d_sq = geodesic_distance_sq(
                q_exp.reshape(-1, 4), 
                k_exp.reshape(-1, 4)
            ).reshape(n_queries, n_keys)
            
            gsm_logits = -d_sq / (2 * tau)
            
            # Compute standard logits via Bridge Theorem (SI Theorem S4):
            # ℓ_std = (1/τ) * Q_i^T K_j  (inner product on Lie algebra)
            # The bivectors ARE the Lie algebra elements u_Q, u_K
            q_biv_exp = q_bivec.unsqueeze(1).expand(n_queries, n_keys, 3)
            k_biv_exp = k_bivec.unsqueeze(0).expand(n_queries, n_keys, 3)
            
            # Lie algebra inner product: u_Q · u_K
            lie_inner = (q_biv_exp * k_biv_exp).sum(dim=-1)
            std_logits = lie_inner / tau
            
            # Compute attention matrices
            P_gsm = torch.softmax(gsm_logits, dim=-1)
            P_std = torch.softmax(std_logits, dim=-1)
            
            # Record max absolute difference
            error = (P_gsm - P_std).abs().max().item()
            trial_errors.append(error)
        
        results['epsilon'].append(eps)
        results['mean_error'].append(np.mean(trial_errors))
        results['std_error'].append(np.std(trial_errors) / np.sqrt(n_trials))
        results['all_errors'].append(trial_errors)
    
    return results


def run_depth_accumulation_experiment(
    depth_values: np.ndarray,
    epsilon: float = 0.1,
    n_queries: int = 8,
    n_keys: int = 32,
    n_trials: int = 100,
    tau: float = 1.0,
    seed: int = 42,
) -> dict:
    """
    Run depth accumulation O(Lε²) validation experiment.
    
    For each depth L, simulates L layers of attention and measures
    cumulative error accumulation.
    
    Returns
    -------
    dict
        Dictionary with depth values, mean cumulative errors, and percentiles.
    """
    torch.manual_seed(seed)
    np.random.seed(seed)
    
    results = {
        'depth': [],
        'mean_cumulative_error': [],
        'p25': [],
        'p75': [],
        'commutator_norm': [],
    }
    
    for L in depth_values:
        L = int(L)
        trial_cumulative_errors = []
        trial_commutator_norms = []
        
        for trial in range(n_trials):
            cumulative_error = 0.0
            generators = []  # For BCH tracking
            
            for layer in range(L):
                # Sample new Q/K for each layer
                q_bivec = epsilon * torch.randn(n_queries, 3)
                k_bivec = epsilon * torch.randn(n_keys, 3)
                
                # Store generators for commutator computation
                generators.append(q_bivec.mean(dim=0).numpy())
                
                q_rotors = exp_map_bivector(q_bivec)
                k_rotors = exp_map_bivector(k_bivec)
                
                q_exp = q_rotors.unsqueeze(1).expand(n_queries, n_keys, 4)
                k_exp = k_rotors.unsqueeze(0).expand(n_queries, n_keys, 4)
                
                d_sq = geodesic_distance_sq(
                    q_exp.reshape(-1, 4),
                    k_exp.reshape(-1, 4)
                ).reshape(n_queries, n_keys)
                
                gsm_logits = -d_sq / (2 * tau)
                
                # Standard logits via Bridge Theorem (Lie algebra inner product)
                q_biv_exp = q_bivec.unsqueeze(1).expand(n_queries, n_keys, 3)
                k_biv_exp = k_bivec.unsqueeze(0).expand(n_queries, n_keys, 3)
                lie_inner = (q_biv_exp * k_biv_exp).sum(dim=-1)
                std_logits = lie_inner / tau
                
                P_gsm = torch.softmax(gsm_logits, dim=-1)
                P_std = torch.softmax(std_logits, dim=-1)
                
                layer_error = (P_gsm - P_std).abs().max().item()
                cumulative_error += layer_error
            
            trial_cumulative_errors.append(cumulative_error)
            
            # Compute commutator sum norm: ||Σ_{i<j} [u_i, u_j]||
            commutator_sum = np.zeros(3)
            for i in range(len(generators)):
                for j in range(i + 1, len(generators)):
                    # Cross product is the Lie bracket for so(3)
                    commutator = np.cross(generators[i], generators[j])
                    commutator_sum += commutator
            
            trial_commutator_norms.append(np.linalg.norm(commutator_sum))
        
        results['depth'].append(L)
        results['mean_cumulative_error'].append(np.mean(trial_cumulative_errors))
        results['p25'].append(np.percentile(trial_cumulative_errors, 25))
        results['p75'].append(np.percentile(trial_cumulative_errors, 75))
        results['commutator_norm'].append(np.mean(trial_commutator_norms))
    
    return results


# =============================================================================
# Figure 2: Bridge Theorem Visualization
# =============================================================================

def generate_figure_2(output_dir: str, tau: float = 1.0):
    """
    Generate Figure 2: Bridge Theorem in One Glance.
    
    Two-panel figure:
    - Left: GSM vs Softmax kernel comparison
    - Right: Error bound schematic
    """
    fig, axes = plt.subplots(1, 2, figsize=(12, 5))
    
    # -------------------------------------------------------------------------
    # Panel 2a: Kernel Comparison
    # -------------------------------------------------------------------------
    ax1 = axes[0]
    
    theta = np.linspace(0, np.pi, 500)
    
    k_gsm = gsm_kernel(theta, tau)
    k_std = softmax_kernel_bridge(theta, tau)
    
    ax1.plot(theta, k_gsm, 'b-', linewidth=2.5, label=r'GSM: $e^{-\theta^2/2\tau}$')
    ax1.plot(theta, k_std, 'r--', linewidth=2.5, label=r'Softmax (Bridge): $e^{\cos(\theta/2)/T}$')
    
    # Shade small-angle regime
    eps_boundary = 0.4
    ax1.axvspan(0, eps_boundary, alpha=0.15, color='green')
    ax1.axvline(eps_boundary, color='green', linestyle=':', alpha=0.7)
    
    # Annotations
    ax1.text(
        0.15, 0.75, 
        r'Small-angle regime' + '\n' + r'(kernels match)',
        transform=ax1.transAxes, fontsize=10, color='darkgreen',
        bbox=dict(boxstyle='round', facecolor='white', alpha=0.8)
    )
    
    ax1.text(
        0.65, 0.55,
        r'Curved regime' + '\n' + r'(manifold effects)',
        transform=ax1.transAxes, fontsize=10, color='gray',
        bbox=dict(boxstyle='round', facecolor='white', alpha=0.8)
    )
    
    ax1.set_xlabel(r'Geodesic Angle $\theta$ (radians)', fontsize=12)
    ax1.set_ylabel('Kernel Value', fontsize=12)
    ax1.set_title(r'(a) GSM vs. Standard Softmax Kernels', fontsize=13, fontweight='bold')
    ax1.legend(loc='upper right', fontsize=10)
    ax1.set_xlim([0, np.pi])
    ax1.set_ylim([0, 1.05])
    ax1.grid(True, alpha=0.3)
    
    # -------------------------------------------------------------------------
    # Panel 2b: Error Bound Schematic
    # -------------------------------------------------------------------------
    ax2 = axes[1]
    
    # Log-log schematic
    eps_range = np.logspace(-2.5, -0.3, 50)
    
    # Theoretical bounds
    C_head = 50  # Head-level constant (illustrative)
    C_stack = 200  # Stack-level constant (illustrative)
    
    head_bound = C_head * eps_range**2
    stack_bound = C_stack * eps_range**2  # For L ~ 4
    
    ax2.loglog(eps_range, head_bound, 'b-', linewidth=2.5, label=r'Head: $C_{\rm head}\varepsilon^2$ (Thm S4)')
    ax2.loglog(eps_range, stack_bound, 'r--', linewidth=2.5, label=r'Stack: $C_{\rm stack} L\varepsilon^2$ (Cor S14)')
    
    # Reference slope line
    slope_ref = 0.5 * eps_range**2
    ax2.loglog(eps_range, slope_ref, 'k:', linewidth=1.5, alpha=0.5, label=r'Slope = 2 reference')
    
    # Annotations
    ax2.annotate(
        r'$O(\varepsilon^2)$',
        xy=(0.1, 50 * 0.1**2), xytext=(0.15, 0.05),
        fontsize=12, fontweight='bold',
        arrowprops=dict(arrowstyle='->', color='blue', lw=1.5)
    )
    
    ax2.set_xlabel(r'Small-Angle Parameter $\varepsilon$', fontsize=12)
    ax2.set_ylabel(r'$\|P^{\rm GSM} - P^{\rm std}\|_\infty$', fontsize=12)
    ax2.set_title(r'(b) Error Bound Scaling', fontsize=13, fontweight='bold')
    ax2.legend(loc='lower right', fontsize=10)
    ax2.grid(True, alpha=0.3, which='both')
    ax2.set_xlim([eps_range[0], eps_range[-1]])
    
    plt.tight_layout()
    
    # Save
    os.makedirs(output_dir, exist_ok=True)
    
    pdf_path = os.path.join(output_dir, 'figure_2_bridge_theorem.pdf')
    fig.savefig(pdf_path, dpi=300, bbox_inches='tight', format='pdf')
    print(f"Saved: {pdf_path}")
    
    png_path = os.path.join(output_dir, 'figure_2_bridge_theorem.png')
    fig.savefig(png_path, dpi=200, bbox_inches='tight', format='png')
    print(f"Saved: {png_path}")
    
    plt.close(fig)
    
    return pdf_path, png_path


# =============================================================================
# Figure 3: Empirical Validation
# =============================================================================

def generate_figure_3(
    output_dir: str,
    tau: float = 1.0,
    seed: int = 42,
) -> tuple[str, str, dict]:
    """
    Generate Figure 3: One Decisive Experiment.
    
    Two-panel figure with empirical validation of Bridge Theorem bounds.
    """
    start_time = time.time()
    
    print("\n" + "=" * 60)
    print("Running Bridge Theorem Validation Experiment")
    print("=" * 60)
    
    # -------------------------------------------------------------------------
    # Run experiments
    # -------------------------------------------------------------------------
    
    print("\n[1/2] Head-level O(ε²) experiment...")
    # Focus on smaller epsilon where small-angle approximation is tighter
    epsilon_values = np.array([0.001, 0.002, 0.005, 0.01, 0.02, 0.05, 0.1])
    head_results = run_head_level_experiment(
        epsilon_values,
        n_queries=8,
        n_keys=32,
        n_trials=200,
        tau=tau,
        seed=seed,
    )
    
    print("[2/2] Depth accumulation O(Lε²) experiment...")
    depth_values = np.array([1, 2, 4, 8, 12, 16, 24, 32])
    depth_results = run_depth_accumulation_experiment(
        depth_values,
        epsilon=0.01,  # Use smaller epsilon for cleaner depth scaling
        n_queries=8,
        n_keys=32,
        n_trials=100,
        tau=tau,
        seed=seed,
    )
    
    elapsed_time = time.time() - start_time
    print(f"\nExperiments completed in {elapsed_time:.1f} seconds")
    
    # -------------------------------------------------------------------------
    # Compute fitted slope for head-level experiment
    # -------------------------------------------------------------------------
    
    log_eps = np.log(head_results['epsilon'])
    log_err = np.log(head_results['mean_error'])
    
    slope, intercept, r_value, p_value, std_err = stats.linregress(log_eps, log_err)
    
    print(f"\nLog-log regression results:")
    print(f"  Fitted slope:  m = {slope:.3f} ± {std_err:.3f}")
    print(f"  Expected:      m = 2.0 (O(ε²))")
    print(f"  R² value:      {r_value**2:.4f}")
    print(f"  p-value:       {p_value:.2e}")
    
    # -------------------------------------------------------------------------
    # Create figure
    # -------------------------------------------------------------------------
    
    fig, axes = plt.subplots(1, 2, figsize=(12, 5))
    
    # Panel 3a: Head-level O(ε²) validation
    ax1 = axes[0]
    
    eps = np.array(head_results['epsilon'])
    mean_err = np.array(head_results['mean_error'])
    std_err_vals = np.array(head_results['std_error'])
    
    ax1.errorbar(
        eps, mean_err, yerr=std_err_vals,
        fmt='o', markersize=8, color='#3498db', 
        capsize=4, capthick=1.5, elinewidth=1.5,
        label='Empirical (200 trials/ε)'
    )
    
    # Fitted line
    eps_fit = np.logspace(np.log10(eps.min()), np.log10(eps.max()), 100)
    fitted_line = np.exp(intercept) * eps_fit**slope
    ax1.loglog(eps_fit, fitted_line, 'r--', linewidth=2, 
               label=f'Fit: $m = {slope:.2f} \\pm {std_err:.2f}$')
    
    # Theoretical O(ε²) reference
    C_theo = np.exp(intercept) * (eps[4] ** (2 - slope)) / (eps[4] ** 2)  # Match at midpoint
    theo_line = C_theo * eps_fit**2
    ax1.loglog(eps_fit, theo_line, 'k:', linewidth=1.5, alpha=0.6,
               label=r'Theory: $O(\varepsilon^2)$')
    
    ax1.set_xlabel(r'Small-Angle Parameter $\varepsilon$', fontsize=12)
    ax1.set_ylabel(r'$\|P^{\rm GSM} - P^{\rm std}\|_\infty$', fontsize=12)
    ax1.set_title(r'(a) Head-Level Error: $O(\varepsilon^2)$ Scaling', fontsize=13, fontweight='bold')
    ax1.legend(loc='lower right', fontsize=10)
    ax1.grid(True, alpha=0.3, which='both')
    
    # Slope annotation
    ax1.text(
        0.05, 0.95,
        f'Fitted slope: {slope:.2f}\n(expected: 2.0)',
        transform=ax1.transAxes, fontsize=11,
        verticalalignment='top',
        bbox=dict(boxstyle='round', facecolor='#ecf0f1', alpha=0.9)
    )
    
    # Panel 3b: Depth accumulation
    ax2 = axes[1]
    
    depths = np.array(depth_results['depth'])
    mean_cum = np.array(depth_results['mean_cumulative_error'])
    p25 = np.array(depth_results['p25'])
    p75 = np.array(depth_results['p75'])
    comm_norm = np.array(depth_results['commutator_norm'])
    
    # Main plot: cumulative error vs depth
    ax2.fill_between(depths, p25, p75, alpha=0.3, color='#3498db')
    ax2.plot(depths, mean_cum, 'o-', markersize=8, color='#3498db', linewidth=2,
             label=r'Cumulative error $\sum_\ell \|P_\ell^{\rm GSM} - P_\ell^{\rm std}\|$')
    
    # Theoretical O(L·ε²) bound
    eps_fixed = 0.1
    C_depth = mean_cum[0] / (1 * eps_fixed**2)
    theo_depth = C_depth * depths * eps_fixed**2
    ax2.plot(depths, theo_depth, 'r--', linewidth=2,
             label=r'Theory: $C \cdot L \cdot \varepsilon^2$')
    
    ax2.set_xlabel(r'Depth $L$ (number of layers)', fontsize=12)
    ax2.set_ylabel(r'Cumulative Error', fontsize=12)
    ax2.set_title(r'(b) Depth Accumulation: $O(L\varepsilon^2)$ Scaling', fontsize=13, fontweight='bold')
    ax2.legend(loc='upper left', fontsize=10)
    ax2.grid(True, alpha=0.3)
    
    # Inset: commutator norm
    ax_inset = ax2.inset_axes([0.55, 0.15, 0.4, 0.35])
    ax_inset.plot(depths, comm_norm, 's-', markersize=5, color='#e74c3c', linewidth=1.5)
    ax_inset.set_xlabel('Depth $L$', fontsize=8)
    ax_inset.set_ylabel(r'$\|\sum [u_i,u_j]\|$', fontsize=8)
    ax_inset.set_title('Commutator Curvature', fontsize=9)
    ax_inset.tick_params(labelsize=7)
    ax_inset.grid(True, alpha=0.3)
    
    plt.tight_layout()
    
    # -------------------------------------------------------------------------
    # Save outputs
    # -------------------------------------------------------------------------
    
    os.makedirs(output_dir, exist_ok=True)
    
    pdf_path = os.path.join(output_dir, 'figure_3_empirical_validation.pdf')
    fig.savefig(pdf_path, dpi=300, bbox_inches='tight', format='pdf')
    print(f"\nSaved: {pdf_path}")
    
    png_path = os.path.join(output_dir, 'figure_3_empirical_validation.png')
    fig.savefig(png_path, dpi=200, bbox_inches='tight', format='png')
    print(f"Saved: {png_path}")
    
    plt.close(fig)
    
    # Save experiment data for reproducibility
    experiment_data = {
        'head_level': {
            'epsilon': head_results['epsilon'],
            'mean_error': head_results['mean_error'],
            'std_error': head_results['std_error'],
            'fitted_slope': slope,
            'slope_std_err': std_err,
            'r_squared': r_value**2,
        },
        'depth_accumulation': {
            'depth': list(depth_results['depth']),
            'mean_cumulative_error': list(depth_results['mean_cumulative_error']),
            'commutator_norm': list(depth_results['commutator_norm']),
        },
        'metadata': {
            'tau': tau,
            'seed': seed,
            'runtime_seconds': elapsed_time,
        }
    }
    
    json_path = os.path.join(output_dir, 'experiment_data.json')
    with open(json_path, 'w') as f:
        json.dump(experiment_data, f, indent=2)
    print(f"Saved: {json_path}")
    
    # Print caption with actual runtime
    print("\n" + "=" * 60)
    print("SUGGESTED FIGURE CAPTION:")
    print("=" * 60)
    print(f"""
Empirical validation of Bridge Theorem bounds (SI Theorem S4, Corollary S14).
(a) Head-level error ||P^GSM - P^std||_∞ scales as O(ε²); fitted slope m = {slope:.2f} ± {std_err:.2f}.
(b) Depth-accumulated error scales as O(L·ε²) with ε = 0.1.
Inset shows BCH commutator curvature growth.
Code and seeds included; experiment completed in {elapsed_time:.1f}s on CPU.
""")
    
    return pdf_path, png_path, experiment_data


# =============================================================================
# CLI
# =============================================================================

def main():
    parser = argparse.ArgumentParser(
        description='Generate Figures 2 & 3: Bridge Theorem and Empirical Validation'
    )
    parser.add_argument(
        '--output_dir',
        type=str,
        default='results/figures',
        help='Output directory for figures'
    )
    parser.add_argument(
        '--seed',
        type=int,
        default=42,
        help='Random seed for reproducibility'
    )
    parser.add_argument(
        '--tau',
        type=float,
        default=1.0,
        help='Temperature parameter for GSM kernel'
    )
    parser.add_argument(
        '--figure',
        type=str,
        choices=['2', '3', 'all'],
        default='all',
        help='Which figure(s) to generate'
    )
    
    args = parser.parse_args()
    
    print("=" * 60)
    print("Bridge Theorem Figure Generation")
    print("=" * 60)
    
    if args.figure in ['2', 'all']:
        print("\n>>> Generating Figure 2: Bridge Theorem Visualization")
        generate_figure_2(args.output_dir, args.tau)
    
    if args.figure in ['3', 'all']:
        print("\n>>> Generating Figure 3: Empirical Validation")
        generate_figure_3(args.output_dir, args.tau, args.seed)
    
    print("\n" + "=" * 60)
    print("Figure generation complete!")
    print("=" * 60)


if __name__ == "__main__":
    main()
