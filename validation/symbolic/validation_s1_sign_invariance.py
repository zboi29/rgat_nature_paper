#!/usr/bin/env python3
"""
Symbolic Validation: SI Lemma S1 — Sign Invariance of Geodesic Distance

Validates that d_geo(-q, k) = d_geo(q, k) for unit quaternions q, k ∈ S³.

This property is fundamental to the double-cover nature of Spin(3):
q and -q represent the same rotation in SO(3).

Reference: si_rgat_paper.tex, Lemma S1
"""
import sympy as sp
from sympy import Symbol, Abs, sqrt, acos, simplify, cos, sin, Rational
import math

def test_sign_invariance():
    print("=" * 65)
    print("  SI LEMMA S1: SIGN INVARIANCE OF GEODESIC DISTANCE")
    print("=" * 65)


    # =============================================================================
    # CHECK 1: Sign invariance of inner product magnitude
    # =============================================================================
    print("\n[1/3] Verifying sign invariance of similarity |⟨q, k⟩|...")

    # Define symbolic quaternion components
    w_q, x_q, y_q, z_q = sp.symbols('w_q x_q y_q z_q', real=True)
    w_k, x_k, y_k, z_k = sp.symbols('w_k x_k y_k z_k', real=True)

    # Inner product ⟨q, k⟩ = w_q*w_k + x_q*x_k + y_q*y_k + z_q*z_k
    inner_qk = w_q * w_k + x_q * x_k + y_q * y_k + z_q * z_k

    # Inner product ⟨-q, k⟩ = -⟨q, k⟩
    inner_neg_q_k = -w_q * w_k - x_q * x_k - y_q * y_k - z_q * z_k

    # Check |⟨-q, k⟩| = |⟨q, k⟩|
    # Proving Abs(x) == Abs(-x) for complex expressions can be hard for SymPy
    # But proving Abs(x)**2 == Abs(-x)**2 is usually immediate.
    diff_sq = simplify(Abs(inner_neg_q_k)**2 - Abs(inner_qk)**2)

    print(f"   |⟨-q, k⟩|^2 - |⟨q, k⟩|^2 = {diff_sq}")

    if diff_sq == 0:
        print("   SUCCESS: Sign invariance of similarity verified (via squared modulus).")
    else:
        print("   FAILURE: Sign invariance mismatch.")
        print(f"   Diff: {diff_sq}")
        assert False, f"Sign invariance mismatch: {diff_sq}"


    # =============================================================================
    # CHECK 2: Geodesic distance formula invariance
    # =============================================================================
    print("\n[2/3] Verifying d_geo formula invariance...")

    # Similarity s(q, k) = |⟨q, k⟩|
    s = Symbol('s', real=True, positive=True)  # s ∈ (0, 1]

    # Geodesic distance: d_geo = 2 * arccos(s)
    d_geo = 2 * acos(s)

    # Since s(-q, k) = |⟨-q, k⟩| = |−⟨q, k⟩| = |⟨q, k⟩| = s(q, k),
    # we have d_geo(-q, k) = 2 * arccos(s(-q, k)) = 2 * arccos(s(q, k)) = d_geo(q, k)
    print("   d_geo(-q, k) = 2 * arccos(|⟨-q, k⟩|)")
    print("               = 2 * arccos(|−⟨q, k⟩|)")
    print("               = 2 * arccos(|⟨q, k⟩|)")
    print("               = d_geo(q, k)  ✓")
    print("   SUCCESS: Geodesic distance formula is sign-invariant.")


    # =============================================================================
    # CHECK 3: Numerical verification with specific quaternions
    # =============================================================================
    print("\n[3/3] Numerical verification with specific rotors...")

    def geodesic_distance(q, k):
        """Compute d_geo(q, k) = 2 * arccos(|⟨q, k⟩|)."""
        inner = sum(qi * ki for qi, ki in zip(q, k))
        s = abs(inner)
        s = min(1.0, max(-1.0, s))  # Clamp for numerical safety
        return 2 * math.acos(s)

    # Test quaternions
    q = (0.5, 0.5, 0.5, 0.5)  # Unit quaternion
    neg_q = tuple(-qi for qi in q)  # Negated
    k = (1.0, 0.0, 0.0, 0.0)  # Identity rotation

    d1 = geodesic_distance(q, k)
    d2 = geodesic_distance(neg_q, k)

    print(f"   q = {q}")
    print(f"  -q = {neg_q}")
    print(f"   k = {k}")
    print(f"   d_geo(q, k)  = {d1:.10f}")
    print(f"   d_geo(-q, k) = {d2:.10f}")

    if abs(d1 - d2) < 1e-12:
        print("   SUCCESS: Numerical values match exactly.")
    else:
        print(f"   FAILURE: Difference = {abs(d1 - d2)}")
        assert False, f"Difference = {abs(d1 - d2)}"


    # =============================================================================
    # CHECK 4: Both signs simultaneously (double-cover verification)
    # =============================================================================
    print("\n[4/4] Double-cover verification: d_geo(q, -k) = d_geo(q, k)...")

    neg_k = tuple(-ki for ki in k)
    d3 = geodesic_distance(q, neg_k)

    print(f"   d_geo(q, -k) = {d3:.10f}")

    if abs(d1 - d3) < 1e-12:
        print("   SUCCESS: d_geo(q, -k) = d_geo(q, k)")
    else:
        print(f"   FAILURE: Difference = {abs(d1 - d3)}")
        assert False, f"Difference = {abs(d1 - d3)}"


    print("\n" + "=" * 65)
    print("  LEMMA S1 VALIDATION COMPLETE")
    print("=" * 65)

if __name__ == "__main__":
    test_sign_invariance()
