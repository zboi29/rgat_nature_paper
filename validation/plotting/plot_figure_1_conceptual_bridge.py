#!/usr/bin/env python3
"""
Figure 1: The Conceptual Bridge — S³/Spin(3) Geometric Visualization

Generates a publication-quality figure showing:
- Main panel: Keys/queries as rotors on S³, geodesic arcs, heat-kernel attention
- Inset: Euclidean/flat-chart limit showing Gaussian kernel in tangent space

This figure communicates "Transformer is a limit case" of the curved geometric
operator family, making the RGAT architecture feel inevitable rather than bespoke.

References
----------
- Nature paper: rgat_nature.tex (Figure 1 placeholder)
- SI: Lemma S1 (sign invariance), Theorem S4 (Bridge Theorem)
- Theory: docs/papers/ga_transformer_with_geometric_softmax_v_1.md §4-6
"""
from __future__ import annotations

import argparse
import os
import sys
from pathlib import Path

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import FancyArrowPatch
from mpl_toolkits.mplot3d import proj3d
from mpl_toolkits.mplot3d.art3d import Line3DCollection
import matplotlib.patches as mpatches

# Add project root to path
PROJECT_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(PROJECT_ROOT))

import torch
from gat_aimo3.model.rotor_math import geodesic_angle, heat_kernel_weight
from gat_aimo3.model.embeddings import exp_map_bivector


# =============================================================================
# Utility Functions
# =============================================================================

def rotor_to_3d_projection(rotor: np.ndarray) -> np.ndarray:
    """
    Project a 4D unit quaternion onto 3D using stereographic projection.
    
    Maps S³ → ℝ³ by projecting from the south pole (-1, 0, 0, 0).
    Points near identity (1, 0, 0, 0) map near the origin.
    
    Parameters
    ----------
    rotor : np.ndarray
        Unit quaternion (w, x, y, z) with w = scalar part.
    
    Returns
    -------
    np.ndarray
        3D point (x', y', z').
    """
    w, x, y, z = rotor
    # Stereographic projection from south pole
    denom = 1 + w + 1e-8  # +1 to project from -1
    return np.array([x / denom, y / denom, z / denom])


def geodesic_arc_3d(
    r1: np.ndarray, r2: np.ndarray, n_points: int = 50
) -> np.ndarray:
    """
    Compute a geodesic arc on S³ between two rotors, projected to 3D.
    
    Uses SLERP (spherical linear interpolation) for the great circle path.
    
    Parameters
    ----------
    r1, r2 : np.ndarray
        Unit quaternions (4D).
    n_points : int
        Number of points along the arc.
    
    Returns
    -------
    np.ndarray
        Array of shape (n_points, 3) with projected 3D points.
    """
    # Handle sign ambiguity: choose the shorter arc
    if np.dot(r1, r2) < 0:
        r2 = -r2
    
    # SLERP parameters
    dot = np.clip(np.dot(r1, r2), -1.0, 1.0)
    theta = np.arccos(dot)
    
    if theta < 1e-6:
        # Nearly identical rotors
        return np.array([rotor_to_3d_projection(r1)] * n_points)
    
    t_vals = np.linspace(0, 1, n_points)
    arc_points = []
    
    for t in t_vals:
        # SLERP formula
        s1 = np.sin((1 - t) * theta) / np.sin(theta)
        s2 = np.sin(t * theta) / np.sin(theta)
        r_interp = s1 * r1 + s2 * r2
        r_interp = r_interp / np.linalg.norm(r_interp)
        arc_points.append(rotor_to_3d_projection(r_interp))
    
    return np.array(arc_points)


def draw_sphere_wireframe(ax, n_lat: int = 20, n_lon: int = 30, alpha: float = 0.25):
    """Draw a wireframe sphere representing the visible portion of S³."""
    u = np.linspace(0, 2 * np.pi, n_lon)
    v = np.linspace(0, np.pi, n_lat)
    
    # Scale for stereographic projection visualization
    scale = 1.5
    x = scale * np.outer(np.cos(u), np.sin(v))
    y = scale * np.outer(np.sin(u), np.sin(v))
    z = scale * np.outer(np.ones(np.size(u)), np.cos(v))
    
    # Draw faint surface for depth perception
    ax.plot_surface(x, y, z, color='#e8f4f8', alpha=0.15, edgecolor='none')
    # Draw wireframe on top
    ax.plot_wireframe(x, y, z, color='#34495e', alpha=alpha, linewidth=0.5)


def bivector_to_3d(bivector: np.ndarray) -> np.ndarray:
    """Map bivector (Lie algebra element) to 3D tangent space point."""
    # The bivector IS the 3D tangent vector (scaled by 2 for half-angle)
    return bivector * 2


# =============================================================================
# Main Figure Generation
# =============================================================================

def generate_figure_1(output_dir: str, seed: int = 42):
    """
    Generate Figure 1: The Conceptual Bridge.
    
    Creates a visualization of GSM attention as heat-kernel diffusion on Spin(3)
    with an inset showing the Euclidean Gaussian limit.
    """
    np.random.seed(seed)
    torch.manual_seed(seed)
    
    # -------------------------------------------------------------------------
    # Generate sample rotors
    # -------------------------------------------------------------------------
    
    # Query: near identity (small perturbation)
    query_bivec = torch.tensor([[0.05, 0.02, -0.03]])
    query_rotor = exp_map_bivector(query_bivec).squeeze().numpy()
    
    # Keys: scattered around identity with varying distances
    n_keys = 12
    key_angles = np.linspace(0.1, 0.8, n_keys)  # Different geodesic scales
    key_bivecs = []
    
    for i, angle in enumerate(key_angles):
        # Random direction on unit sphere
        direction = np.random.randn(3)
        direction = direction / np.linalg.norm(direction)
        key_bivecs.append(angle * direction)
    
    key_bivecs = torch.tensor(np.array(key_bivecs), dtype=torch.float32)
    key_rotors = exp_map_bivector(key_bivecs).numpy()
    
    # Compute geodesic distances and heat-kernel weights
    tau = 0.5
    query_tensor = torch.tensor(query_rotor, dtype=torch.float32).unsqueeze(0)
    key_tensors = torch.tensor(key_rotors, dtype=torch.float32)
    
    distances = geodesic_angle(
        query_tensor.expand(n_keys, 4), key_tensors
    ).numpy()
    
    weights = heat_kernel_weight(
        query_tensor.expand(n_keys, 4), 
        key_tensors,
        torch.tensor(tau)
    ).numpy()
    
    # Normalize for visualization
    weights_normalized = weights / weights.max()
    
    # -------------------------------------------------------------------------
    # Create figure with main panel + inset
    # -------------------------------------------------------------------------
    
    fig = plt.figure(figsize=(10, 8))
    
    # Main 3D panel
    ax_main = fig.add_subplot(111, projection='3d')
    
    # Style settings
    ax_main.set_facecolor('white')
    ax_main.xaxis.pane.fill = False
    ax_main.yaxis.pane.fill = False
    ax_main.zaxis.pane.fill = False
    ax_main.xaxis.pane.set_edgecolor('lightgray')
    ax_main.yaxis.pane.set_edgecolor('lightgray')
    ax_main.zaxis.pane.set_edgecolor('lightgray')
    
    # Draw sphere wireframe
    draw_sphere_wireframe(ax_main, alpha=0.3)
    
    # Project rotors to 3D
    query_3d = rotor_to_3d_projection(query_rotor)
    keys_3d = np.array([rotor_to_3d_projection(r) for r in key_rotors])
    
    # Plot query rotor (larger, distinct color)
    ax_main.scatter(
        [query_3d[0]], [query_3d[1]], [query_3d[2]],
        s=200, c='#e74c3c', marker='*', edgecolors='black', linewidths=1,
        label=r'Query $\mu_i$', zorder=10
    )
    
    # Plot key rotors (color by weight)
    cmap = plt.cm.Blues
    for i, (k3d, w) in enumerate(zip(keys_3d, weights_normalized)):
        color = cmap(0.3 + 0.7 * w)  # Map weight to color
        ax_main.scatter(
            [k3d[0]], [k3d[1]], [k3d[2]],
            s=100 + 100 * w, c=[color], marker='o', 
            edgecolors='#2c3e50', linewidths=0.5,
            zorder=5
        )
    
    # Draw geodesic arcs from query to each key
    for i, (key_rotor, w) in enumerate(zip(key_rotors, weights_normalized)):
        arc = geodesic_arc_3d(query_rotor, key_rotor, n_points=30)
        
        # Color and linewidth by attention weight
        color = cmap(0.3 + 0.7 * w)
        linewidth = 0.5 + 2.5 * w
        alpha = 0.3 + 0.7 * w
        
        ax_main.plot(
            arc[:, 0], arc[:, 1], arc[:, 2],
            color=color, linewidth=linewidth, alpha=alpha
        )
    
    # Labels and title
    ax_main.set_xlabel(r'$x$', fontsize=12, labelpad=10)
    ax_main.set_ylabel(r'$y$', fontsize=12, labelpad=10)
    ax_main.set_zlabel(r'$z$', fontsize=12, labelpad=10)
    ax_main.set_title(
        r'Heat-Kernel Diffusion on $\mathrm{Spin}(3)$',
        fontsize=14, fontweight='bold', pad=20
    )
    
    # Add colorbar for attention weights
    sm = plt.cm.ScalarMappable(cmap=cmap, norm=plt.Normalize(0, 1))
    sm.set_array([])
    cbar = fig.colorbar(sm, ax=ax_main, shrink=0.5, aspect=20, pad=0.1)
    cbar.set_label(r'Attention weight $K_{ij} = e^{-d_{\mathrm{geo}}^2/2\tau}$', fontsize=10)
    
    # Set viewing angle
    ax_main.view_init(elev=20, azim=45)
    ax_main.set_box_aspect([1, 1, 1])
    
    # Axis limits
    lim = 1.2
    ax_main.set_xlim([-lim, lim])
    ax_main.set_ylim([-lim, lim])
    ax_main.set_zlim([-lim, lim])
    
    # -------------------------------------------------------------------------
    # Inset: Euclidean/flat-chart limit
    # -------------------------------------------------------------------------
    
    # Create inset axes
    ax_inset = fig.add_axes([0.12, 0.15, 0.28, 0.28])
    ax_inset.set_facecolor('#f8f9fa')
    
    # Project to tangent space (Lie algebra)
    query_tangent = bivector_to_3d(query_bivec.squeeze().numpy())[:2]  # Project to 2D
    keys_tangent = np.array([bivector_to_3d(b.numpy())[:2] for b in key_bivecs])
    
    # Draw Gaussian blob centered at query
    theta_grid = np.linspace(0, 2 * np.pi, 100)
    
    for r_scale in [0.5, 1.0, 1.5, 2.0]:
        radius = r_scale * np.sqrt(2 * tau)  # 1, 2, 3 sigma contours
        x_circle = query_tangent[0] + radius * np.cos(theta_grid)
        y_circle = query_tangent[1] + radius * np.sin(theta_grid)
        alpha = 0.4 - 0.08 * r_scale
        ax_inset.plot(x_circle, y_circle, 'orange', alpha=alpha, linewidth=1)
        ax_inset.fill(x_circle, y_circle, color='orange', alpha=alpha * 0.3)
    
    # Plot tangent space points
    ax_inset.scatter(
        [query_tangent[0]], [query_tangent[1]],
        s=100, c='#e74c3c', marker='*', edgecolors='black', linewidths=0.5,
        zorder=10
    )
    ax_inset.scatter(
        keys_tangent[:, 0], keys_tangent[:, 1],
        s=50, c='#3498db', marker='o', edgecolors='#2c3e50', linewidths=0.3,
        alpha=0.8
    )
    
    # Add formula annotation
    ax_inset.text(
        0.5, 0.95, r'$K \propto e^{-\|u-v\|^2/2\tau}$',
        transform=ax_inset.transAxes, fontsize=9,
        ha='center', va='top', 
        bbox=dict(boxstyle='round', facecolor='white', alpha=0.8)
    )
    
    ax_inset.set_xlabel(r'$u_1$', fontsize=9)
    ax_inset.set_ylabel(r'$u_2$', fontsize=9)
    ax_inset.set_title(r'Flat Chart ($\epsilon \to 0$)', fontsize=10, fontweight='bold')
    ax_inset.set_aspect('equal')
    ax_inset.tick_params(labelsize=7)
    
    # Arrow from inset to main
    ax_inset.annotate(
        '', xy=(1.0, 0.7), xycoords='axes fraction',
        xytext=(1.3, 1.0), textcoords='axes fraction',
        arrowprops=dict(arrowstyle='->', color='gray', lw=1.5)
    )
    
    # -------------------------------------------------------------------------
    # Add equation annotations to main panel
    # -------------------------------------------------------------------------
    
    # Geodesic distance formula
    fig.text(
        0.72, 0.85, 
        r'$d_{\mathrm{geo}}(q,k) = 2\arccos(|\langle q, k \rangle|)$',
        fontsize=11, 
        bbox=dict(boxstyle='round', facecolor='#ecf0f1', alpha=0.9)
    )
    
    # Bridge theorem note
    fig.text(
        0.72, 0.78,
        r'Small-angle: $d_{\mathrm{geo}}^2 \approx 4\|u-v\|^2$',
        fontsize=10, color='#7f8c8d'
    )
    
    # Legend
    ax_main.legend(loc='upper left', fontsize=10)
    
    # -------------------------------------------------------------------------
    # Save figure
    # -------------------------------------------------------------------------
    
    os.makedirs(output_dir, exist_ok=True)
    
    # High-res PDF for Nature
    pdf_path = os.path.join(output_dir, 'figure_1_conceptual_bridge.pdf')
    fig.savefig(pdf_path, dpi=300, bbox_inches='tight', format='pdf')
    print(f"Saved: {pdf_path}")
    
    # PNG preview
    png_path = os.path.join(output_dir, 'figure_1_conceptual_bridge.png')
    fig.savefig(png_path, dpi=200, bbox_inches='tight', format='png')
    print(f"Saved: {png_path}")
    
    plt.close(fig)
    
    return pdf_path, png_path


# =============================================================================
# CLI
# =============================================================================

def main():
    parser = argparse.ArgumentParser(
        description='Generate Figure 1: The Conceptual Bridge (S³ geometry visualization)'
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
    
    args = parser.parse_args()
    
    print("=" * 60)
    print("Generating Figure 1: The Conceptual Bridge")
    print("=" * 60)
    
    pdf_path, png_path = generate_figure_1(args.output_dir, args.seed)
    
    print("\nFigure 1 generation complete!")
    print(f"  PDF: {pdf_path}")
    print(f"  PNG: {png_path}")


if __name__ == "__main__":
    main()
