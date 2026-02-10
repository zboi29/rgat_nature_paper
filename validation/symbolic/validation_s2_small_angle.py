#!/usr/bin/env python3
"""
Symbolic Validation: SI Lemma S2 — Small-angle Distance Expansion

Validates that for small generators u, v with norm <= ε:
    d_geo(exp(u), exp(v))^2 = 4||u - v||^2 + O(ε^4)

This lemma provides the geometric justification for why the curved heat kernel
approximates the flat Gaussian kernel in the high-temperature (small-angle) limit.

Reference: si_rgat_paper.tex, Lemma S2
"""
import sympy as sp
from sympy import Symbol, symbols, exp, Rational, simplify, cos, sin, acos, sqrt, series, Matrix

def test_small_angle_expansion():
    print("=" * 65)
    print("  SI LEMMA S2: SMALL-ANGLE DISTANCE EXPANSION")
    print("=" * 65)

    # We will work with a simplified 3D rotor model (quaternions)
    # q = exp(u), where u is a pure imaginary quaternion vector.
    # For small u, exp(u) approx 1 + u + u^2/2 + ...
    # We verify the expansion order by scaling u -> t*u and expanding in t via taylor series at t=0

    # 1. Define symbolic vector variables
    t = Symbol('t', real=True) # Scaling parameter (represents epsilon)
    
    # Let u and v be 3D vectors
    u1, u2, u3 = symbols('u1 u2 u3', real=True)
    v1, v2, v3 = symbols('v1 v2 v3', real=True)
    
    # Squared Euclidean distance: ||u - v||^2
    euclidean_dist_sq = (u1 - v1)**2 + (u2 - v2)**2 + (u3 - v3)**2
    
    print("\n[1/3] Defining Rotor Exponentials...")

    # Quaternion multiplication helper
    def quat_mul(q1, q2):
        w1, x1, y1, z1 = q1
        w2, x2, y2, z2 = q2
        return (
            w1*w2 - x1*x2 - y1*y2 - z1*z2,
            w1*x2 + x1*w2 + y1*z2 - z1*y2,
            w1*y2 - x1*z2 + y1*w2 + z1*x2,
            w1*z2 + x1*y2 - y1*x2 + z1*w2
        )

    # Exponential map for pure vector u=(0, a, b, c) with norm theta
    # exp(u) = (cos(theta), sin(theta)*a/theta, ...)
    def quat_exp(vx, vy, vz, scale):
        # We perform scaling inside
        vx, vy, vz = vx*scale, vy*scale, vz*scale
        theta_sq = vx**2 + vy**2 + vz**2
        theta = sqrt(theta_sq)
        
        # Sinc approximation for stability (symbolic cancellation handles this, but explicit form is safer)
        # However, for pure symbolic expansion at t=0, we can use the explicit sin/cos forms directly
        # and SymPy's series expansion handles the limit behavior.
        
        w = cos(theta)
        s = sin(theta) / theta # This is sinc(theta)
        
        # When theta->0, s->1. SymPy handles standard limit well.
        return (w, s*vx, s*vy, s*vz)

    # Compute q(t) and k(t)
    q = quat_exp(u1, u2, u3, t)
    k = quat_exp(v1, v2, v3, t)

    print("   q(t) = exp(t*u)")
    print("   k(t) = exp(t*v)")

    # 2. Compute Geodesic Distance
    print("\n[2/3] Computing Geodesic Distance Expansion...")
    
    # inner product <q, k>
    inner = sum(a*b for a, b in zip(q, k))
    
    # d_geo(q, k) = 2 * arccos(|<q, k>|)
    # Since for small t, <q, k> is close to 1, we don't need abs() if checking near t=0
    # Let's perform series expansion of s = <q, k>
    
    # Series expansion of inner product up to order t^4
    s_series = series(inner, t, 0, 5).removeO()
    print(f"   <q, k> approx = {s_series}")
    
    # arccos(x) expansion around x=1:
    # arccos(1 - delta) = sqrt(2*delta) + ...
    # Instead of manual composition, let SymPy handle d_geo^2 expansion
    
    # We want d_geo^2 = 4 * arccos(s)^2
    # Caution: arccos(s) derivative at s=1 is singular.
    # But s = 1 - alpha*t^2 + ...
    # arccos(1 - y) ~ sqrt(2y). So arccos(..) ~ sqrt(2 * alpha * t^2) ~ sqrt(2*alpha)*t
    # So d^2 ~ 4 * (2*alpha*t^2) ~ 8*alpha*t^2
    
    # Let's verify expansion of 4 * arccos(s_series)^2
    d_geo_sq_expr = 4 * acos(s_series)**2
    d_geo_expansion = series(d_geo_sq_expr, t, 0, 5).removeO()
    
    print(f"   d_geo^2 expansion = {d_geo_expansion}")

    # 3. Verify Match with Euclidean Distance
    print("\n[3/3] Verifying S2 Identity...")
    
    # Target: 4 * ||t(u-v)||^2 = 4 * t^2 * ||u-v||^2
    target_euclidean = 4 * t**2 * euclidean_dist_sq
    
    # Check difference
    diff = simplify(d_geo_expansion - target_euclidean)
    print(f"   Difference (d_geo^2 - 4||u-v||^2) = {diff}")
    
    # We expect the O(t^2) term to cancel out exactly.
    # The remainder will be O(t^3) or O(t^4). Lemma says |...| <= C epsilon^4
    # which implies the error term is order t^4. 
    # Actually, curvature [u, v] terms appear at t^4 order in squared distance (t^2 in distance).
    # Wait, BCH says w = u - v + O(t^2). d = 2|w| = 2|u-v| + O(t^3).
    # d^2 = 4|u-v|^2 + O(t^4).
    # So we expect NO t^2 or t^3 terms in the difference.
    
    # Let's check coefficients of t^0, t^1, t^2, t^3
    coeffs = [diff.coeff(t, i) for i in range(4)]
    
    if all(simplify(c) == 0 for c in coeffs):
        print("   SUCCESS: Leading terms match. Error is O(t^4).")
        print("   d_geo(q, k)^2 = 4||u-v||^2 + O(ε^4) confirmed.")
    else:
        print("   FAILURE: Lower order terms found in difference.")
        print(f"   Coeffs [0-3]: {coeffs}")
        assert False, "Expansion mismatch"

    print("\n" + "=" * 65)
    print("  LEMMA S2 VALIDATION COMPLETE")
    print("=" * 65)

if __name__ == "__main__":
    test_small_angle_expansion()
