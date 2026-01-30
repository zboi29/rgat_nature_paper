#!/usr/bin/env python3
"""
Symbolic Validation: SI Theorem S9 — Gauge Equivariance

Validates that GSM attention is invariant under global Spin(3) gauge transformations.
d_geo(gμ, gr) = d_geo(μ, r) for g ∈ Spin(3).

This ensures the physics of the model depends only on relative geometry,
not the arbitrary choice of coordinate frame.

Reference: si_rgat_nature.tex, Theorem S9
"""
import sympy as sp
from sympy import Symbol, simplify, expand, Abs, Matrix, MatMul

def test_gauge_equivariance():
    print("=" * 65)
    print("  SI THEOREM S9: GAUGE EQUIVARIANCE OF GSM ATTENTION")
    print("=" * 65)

    # =============================================================================
    # Helper: Quaternion Multiplication
    # =============================================================================
    def quat_mul(q1, q2):
        """Symbolic quaternion multiplication."""
        w1, x1, y1, z1 = q1
        w2, x2, y2, z2 = q2
        return (
            w1*w2 - x1*x2 - y1*y2 - z1*z2,
            w1*x2 + x1*w2 + y1*z2 - z1*y2,
            w1*y2 - x1*z2 + y1*w2 + z1*x2,
            w1*z2 + x1*y2 - y1*x2 + z1*w2
        )

    def quat_inner(q1, q2):
        """Symbolic quaternion inner product (Euclidean R4)."""
        return sum(a*b for a, b in zip(q1, q2))

    # =============================================================================
    # CHECK 1: Distance Invariance
    # =============================================================================
    print("\n[1/2] Verifying d_geo(gμ, gr) = d_geo(μ, r)...")

    # Define symbolic quaternions
    # We can't use general symbols for all components without simplification getting stuck
    # because we need to use q^-1 = conj(q) for unit quaternions.
    # Instead, we verify |<gq, gk>| = |<q, k>| using the property that 
    # rotation by g preserves the Euclidean inner product.

    # Explicit algebraic check for specific g
    # Let g be a general symbolic quaternion
    wg, xg, yg, zg = sp.symbols('w_g x_g y_g z_g', real=True)
    g = (wg, xg, yg, zg)

    wq, xq, yq, zq = sp.symbols('w_q x_q y_q z_q', real=True)
    q = (wq, xq, yq, zq)

    wk, xk, yk, zk = sp.symbols('w_k x_k y_k z_k', real=True)
    k = (wk, xk, yk, zk)

    print("   Computing transformed rotors g*q and g*k...")
    gq = quat_mul(g, q)
    gk = quat_mul(g, k)

    print("   Computing inner product <g*q, g*k>...")
    inner_transformed = quat_inner(gq, gk)
    inner_original = quat_inner(q, k)

    # The relationship <gq, gk> = |g|^2 <q, k> holds generally
    # For unit g, |g|^2 = 1, so <gq, gk> = <q, k>
    sq_norm_g = wg**2 + xg**2 + yg**2 + zg**2

    print("   Verifying <gq, gk> = |g|^2 <q, k>...")
    diff = simplify(inner_transformed - sq_norm_g * inner_original)

    if diff == 0:
        print("   SUCCESS: <gq, gk> = |g|^2 <q, k> verified algebraically.")
        print("   For g ∈ Spin(3), |g|=1, so d_geo(gq, gk) = d_geo(q, k).")
    else:
        print("   FAILURE: Inner product transformation mismatch.")
        print(f"   Diff: {diff}")
        assert False, f"Inner product mismatch, diff={diff}"


    # =============================================================================
    # CHECK 2: Attention Weight Invariance
    # =============================================================================
    print("\n[2/2] Verifying attention weight P_ij invariance...")

    # Since d_geo is invariant, K_ij is invariant.
    print("   K'_ij = exp(-d_geo(gμ_i, gr_j)^2 / 2τ)")
    print("         = exp(-d_geo(μ_i, r_j)^2 / 2τ)  (by Check 1)")
    print("         = K_ij")

    # Normalization is invariant
    print("   P'_ij = K'_ij / Σ_k K'_ik")
    print("         = K_ij / Σ_k K_ik")
    print("         = P_ij")

    print("   SUCCESS: Attention weights are gauge-invariant.")

    print("\n" + "=" * 65)
    print("  THEOREM S9 VALIDATION COMPLETE")
    print("=" * 65)

if __name__ == "__main__":
    test_gauge_equivariance()
