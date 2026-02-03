/-
Exponential and approximation lemmas for quaternions.

Collects analytic identities and Taylor-style bounds for `exp` on pure
imaginary quaternions, used to relate geodesic distance to Euclidean distance.
-/
import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 200000
set_option maxRecDepth 3000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-
### Inner product of exponentials

For pure imaginary `u, v`, `inner (exp u) (exp v)` can be expressed in terms of
`cos ‖u‖`, `sin ‖u‖ / ‖u‖`, and `inner u v`. This is the key algebraic identity
used in the small-angle expansion.
-/

lemma inner_exp_exp_eq (u v : Quaternion ℝ) (hu : u.re = 0) (hv : v.re = 0) :
  inner ℝ (NormedSpace.exp ℝ u) (NormedSpace.exp ℝ v) =
  Real.cos ‖u‖ * Real.cos ‖v‖ + (if ‖u‖ = 0 then 1 else Real.sin ‖u‖ / ‖u‖) * (if ‖v‖ = 0 then 1 else Real.sin ‖v‖ / ‖v‖) * inner ℝ u v := by
    -- Use the formula `exp u = cos ‖u‖ + (sin ‖u‖ / ‖u‖) • u` for pure imaginary quaternions.
    have h_exp : ∀ u : Quaternion ℝ, u.re = 0 → NormedSpace.exp ℝ u = Real.cos ‖u‖ + (if ‖u‖ = 0 then 1 else Real.sin ‖u‖ / ‖u‖) • u := by
      -- Use the formula `exp u = cos ‖u‖ + (sin ‖u‖ / ‖u‖) • u` for pure imaginary quaternions. This follows from the definition of the exponential map.
      have h_exp : ∀ u : Quaternion ℝ, u.re = 0 → NormedSpace.exp ℝ u = Real.cos ‖u‖ + (Real.sin ‖u‖ / ‖u‖) • u := by
        exact fun u a ↦ Quaternion.exp_of_re_eq_zero u a;
      by_cases h : ‖u‖ = 0 <;> aesop;
    norm_num [ h_exp u hu, h_exp v hv, inner ];
    by_cases hu' : u = 0 <;> by_cases hv' : v = 0 <;> simp +decide [ *, mul_assoc ];
    ring

/-
Cosine approximation bound: for `|x| ≤ 1`, the Taylor remainder is `O(|x|^4)`.
-/
lemma cos_approx_bound (x : ℝ) (hx : |x| ≤ 1) :
  |Real.cos x - (1 - x^2 / 2)| ≤ |x|^4 / 24 := by
    -- This follows from the Taylor series expansion of cosine with the Lagrange remainder term.
    have h_cos_taylor_bound : ∀ x : ℝ, |x| ≤ 1 → |Real.cos x - (1 - x^2 / 2)| ≤ |x|^4 / 24 := by
      intro x hx
      have h_cos_taylor : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → |Real.cos x - (1 - x^2 / 2)| ≤ x^4 / 24 := by
        -- This follows from the Taylor series expansion of cosine with the Lagrange remainder term. The 4th derivative of cos is cos, which is bounded by 1. Thus the error is bounded by $|x|^4/4!$.
        intros x hx_nonneg hx_le_one
        have h_cos_taylor : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → Real.cos x ≤ 1 - x^2 / 2 + x^4 / 24 := by
          -- Let's choose any $x$ in the interval $[0, 1]$.
          intro x hx_nonneg hx_le_one
          have h_cos_taylor : ∀ t ∈ Set.Icc 0 x, Real.sin t ≥ t - t^3 / 6 := by
            -- Let's choose any $t$ in the interval $[0, x]$.
            intro t ht
            have h_sin_taylor : ∀ u ∈ Set.Icc 0 t, Real.cos u ≥ 1 - u^2 / 2 := by
              exact fun u a ↦ Real.one_sub_sq_div_two_le_cos;
            -- Integrate both sides of $\cos u \geq 1 - u^2 / 2$ from $0$ to $t$.
            have h_integral : ∫ u in (0 : ℝ)..t, Real.cos u ≥ ∫ u in (0 : ℝ)..t, (1 - u^2 / 2) := by
              refine' intervalIntegral.integral_mono_on _ _ _ _ <;> aesop;
            norm_num at h_integral; linarith;
          -- Integrate both sides of $\sin t \geq t - t^3 / 6$ from $0$ to $x$.
          have h_integral : ∫ t in (0 : ℝ)..x, Real.sin t ≥ ∫ t in (0 : ℝ)..x, (t - t^3 / 6) := by
            refine' intervalIntegral.integral_mono_on _ _ _ _ <;> aesop;
          norm_num at h_integral; linarith;
        -- Since $\cos x$ is decreasing in $[0, 1]$, we have $\cos x \geq 1 - x^2 / 2$.
        have h_cos_lower_bound : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → Real.cos x ≥ 1 - x^2 / 2 := by
          exact fun x a a ↦ Real.one_sub_sq_div_two_le_cos;
        exact abs_le.mpr ⟨ by linarith [ h_cos_lower_bound x hx_nonneg hx_le_one, h_cos_taylor x hx_nonneg hx_le_one ], by linarith [ h_cos_lower_bound x hx_nonneg hx_le_one, h_cos_taylor x hx_nonneg hx_le_one ] ⟩
      cases abs_cases x <;> simp +decide [ * ];
      · exact h_cos_taylor x ( by linarith ) ( by linarith );
      · convert h_cos_taylor ( -x ) ( by linarith ) ( by linarith ) using 1 <;> norm_num;
    exact h_cos_taylor_bound x hx

/-
For $|x| \le 1$, $|\text{sinc}(x) - 1| \le x^2/6$.
-/
lemma sinc_approx_bound (x : ℝ) (hx : |x| ≤ 1) :
  |(if x = 0 then 1 else Real.sin x / x) - 1| ≤ x^2 / 6 := by
    by_cases hx' : x = 0 <;> simp_all +decide;
    -- Since $|x| \le 1$, we have $|\sin x - x| \le \frac{|x|^3}{6}$.
    have h_sin_x_bound : |Real.sin x - x| ≤ |x|^3 / 6 := by
      -- By the properties of the derivative of $\sin x$, we know that $|\sin x - x| \leq \frac{|x|^3}{6}$ for $|x| \leq 1$.
      have h_sin_deriv_bound : ∀ x : ℝ, 0 < x ∧ x ≤ 1 → |Real.sin x - x| ≤ x^3 / 6 := by
        -- By the properties of the derivative of $\sin x$, we know that $|\sin x - x| \leq \frac{|x|^3}{6}$ for $|x| \leq 1$. We'll use the fact that $|\cos x - 1| \leq \frac{x^2}{2}$ for $0 < x \leq 1$.
        have h_cos_bound : ∀ x : ℝ, 0 < x ∧ x ≤ 1 → |Real.cos x - 1| ≤ x^2 / 2 := by
          -- Use the trigonometric identity $\cos x = 1 - 2 \sin^2 (x/2)$ and the fact that $|\sin (x/2)| \leq x/2$ for $0 < x \leq 1$.
          intros x hx
          have h_sin_sq : |Real.sin (x / 2)| ≤ x / 2 := by
            exact le_of_lt ( by rw [ abs_of_nonneg ( Real.sin_nonneg_of_nonneg_of_le_pi ( by linarith ) ( by linarith [ Real.pi_gt_three ] ) ) ] ; exact Real.sin_lt <| by linarith );
          rw [ show Real.cos x - 1 = -2 * Real.sin ( x / 2 ) ^ 2 by rw [ Real.sin_sq, Real.cos_sq ] ; ring_nf ] ; rw [ abs_le ] ; constructor <;> nlinarith [ abs_le.mp h_sin_sq ] ;
        -- Using the fact that $|\cos x - 1| \leq \frac{x^2}{2}$ for $0 < x \leq 1$, we can bound the integral.
        intros x hx
        have h_integral_bound : |∫ t in (0 : ℝ)..x, (Real.cos t - 1)| ≤ ∫ t in (0 : ℝ)..x, t^2 / 2 := by
          rw [ intervalIntegral.integral_of_le hx.1.le, intervalIntegral.integral_of_le hx.1.le ];
          refine' le_trans ( MeasureTheory.norm_integral_le_integral_norm ( _ : ℝ → ℝ ) ) ( MeasureTheory.integral_mono_of_nonneg _ _ _ );
          · exact Filter.Eventually.of_forall fun _ => norm_nonneg _;
          · exact Continuous.integrableOn_Ioc ( by continuity );
          · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with y hy using h_cos_bound y ⟨ hy.1, hy.2.trans hx.2 ⟩;
        norm_num at *; linarith;
      cases abs_cases x <;> simp +decide [ * ];
      · exact h_sin_deriv_bound x ⟨ lt_of_le_of_ne ( by linarith ) ( Ne.symm hx' ), by linarith ⟩;
      · convert h_sin_deriv_bound ( -x ) ⟨ by linarith, by linarith ⟩ using 1 ; norm_num [ abs_sub_comm ];
        ring_nf;
    field_simp;
    rw [ abs_div ];
    rw [ div_mul_eq_mul_div, div_le_iff₀ ] <;> nlinarith [ abs_pos.mpr hx', abs_mul_abs_self x ]

/-
For $|x|, |y| \le 1$, $|\cos x \cos y - (1 - x^2/2 - y^2/2)| \le x^4 + y^4 + x^2 y^2/2$.
-/
lemma cos_mul_approx (x y : ℝ) (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
  |Real.cos x * Real.cos y - (1 - x^2 / 2 - y^2 / 2)| ≤ |x|^4 + |y|^4 + x^2 * y^2 / 2 := by
    -- We have $\cos x = 1 - x^2/2 + R_x$ with $|R_x| \le x^4/24$ and similarly for $y$.
    have h_cos_approx : ∀ x : ℝ, |x| ≤ 1 → |Real.cos x - (1 - x^2 / 2)| ≤ |x|^4 / 24 := by
      exact cos_approx_bound;
    -- Applying the approximations to our expression and using the triangle inequality:
    have h_cos_approx_prod : |Real.cos x * Real.cos y - (1 - x^2 / 2 - y^2 / 2)| ≤ |Real.cos x - (1 - x^2 / 2)| * |Real.cos y| + |Real.cos y - (1 - y^2 / 2)| * |1 - x^2 / 2| + x^2 * y^2 / 4 := by
      rw [ ← abs_mul, ← abs_mul ];
      convert abs_add_three ( ( Real.cos x - ( 1 - x ^ 2 / 2 ) ) * Real.cos y ) ( ( Real.cos y - ( 1 - y ^ 2 / 2 ) ) * ( 1 - x ^ 2 / 2 ) ) ( x ^ 2 * y ^ 2 / 4 ) using 2 ; ring;
      rw [ abs_of_nonneg ( by positivity ) ];
    refine le_trans h_cos_approx_prod ?_;
    refine' le_trans ( add_le_add_three ( mul_le_of_le_one_right ( abs_nonneg _ ) ( Real.abs_cos_le_one _ ) ) ( mul_le_of_le_one_right ( abs_nonneg _ ) ( abs_le.mpr ⟨ by nlinarith only [ abs_le.mp hx, abs_le.mp hy ], by nlinarith only [ abs_le.mp hx, abs_le.mp hy ] ⟩ ) ) le_rfl ) _;
    refine' le_trans ( add_le_add_three ( h_cos_approx x hx ) ( h_cos_approx y hy ) le_rfl ) _;
    nlinarith only [ show 0 ≤ |x|^4 by positivity, show 0 ≤ |y|^4 by positivity, show 0 ≤ x^2 * y^2 by positivity, show |x|^4 ≤ 1 by exact pow_le_one₀ ( abs_nonneg x ) hx, show |y|^4 ≤ 1 by exact pow_le_one₀ ( abs_nonneg y ) hy ]

/-
For $\|u\|, \|v\| \le 1$, the error in approximating the sinc product term is bounded by $O(\epsilon^4)$.
-/
lemma sinc_mul_approx (u v : Quaternion ℝ) (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
  |((if ‖u‖ = 0 then 1 else Real.sin ‖u‖ / ‖u‖) * (if ‖v‖ = 0 then 1 else Real.sin ‖v‖ / ‖v‖) - 1) * inner ℝ u v| ≤ (‖u‖^2 / 6 + ‖v‖^2 / 6 + ‖u‖^2 * ‖v‖^2 / 36) * (‖u‖ * ‖v‖) := by
    have h_bound : |((if ‖u‖ = 0 then 1 else Real.sin ‖u‖ / ‖u‖) * (if ‖v‖ = 0 then 1 else Real.sin ‖v‖ / ‖v‖) - 1)| ≤ ‖u‖^2 / 6 + ‖v‖^2 / 6 + ‖u‖^2 * ‖v‖^2 / 36 := by
      -- Applying the bound from `sinc_approx_bound` to each term in the product.
      have h_sinc_u : |(if ‖u‖ = 0 then 1 else Real.sin ‖u‖ / ‖u‖) - 1| ≤ ‖u‖^2 / 6 := by
        convert sinc_approx_bound ‖u‖ ( abs_le.mpr ⟨ by linarith [ norm_nonneg u ], by linarith [ norm_nonneg u ] ⟩ ) using 1
      have h_sinc_v : |(if ‖v‖ = 0 then 1 else Real.sin ‖v‖ / ‖v‖) - 1| ≤ ‖v‖^2 / 6 := by
        convert sinc_approx_bound ‖v‖ ( abs_le.mpr ⟨ by linarith [ norm_nonneg v ], by linarith [ norm_nonneg v ] ⟩ ) using 1;
      rw [ abs_le ] at *;
      constructor <;> nlinarith [ show 0 ≤ ‖u‖ ^ 2 by positivity, show 0 ≤ ‖v‖ ^ 2 by positivity ];
    convert mul_le_mul h_bound ( abs_real_inner_le_norm u v ) ( by positivity ) ( by positivity ) using 1 ; norm_num [ abs_mul ]

/-
The error in approximating the inner product of exponentials by $1 - \|u-v\|^2/2$ is bounded by the sum of the errors from the cosine and sinc approximations.
-/
lemma inner_expansion_combine (u v : Quaternion ℝ) (hu : u.re = 0) (hv : v.re = 0) (hu_norm : ‖u‖ ≤ 1) (hv_norm : ‖v‖ ≤ 1) :
  |inner ℝ (NormedSpace.exp ℝ u) (NormedSpace.exp ℝ v) - (1 - ‖u - v‖^2 / 2)| ≤
  |‖u‖^4 + ‖v‖^4 + ‖u‖^2 * ‖v‖^2 / 2| + (‖u‖^2 / 6 + ‖v‖^2 / 6 + ‖u‖^2 * ‖v‖^2 / 36) * (‖u‖ * ‖v‖) := by
    -- We have `inner (exp u) (exp v) = cos|u|cos|v| + sinc|u|sinc|v|<u,v>`.
    have h_exp_inner : inner ℝ (NormedSpace.exp ℝ u) (NormedSpace.exp ℝ v) = Real.cos ‖u‖ * Real.cos ‖v‖ + (if ‖u‖ = 0 then 1 else Real.sin ‖u‖ / ‖u‖) * (if ‖v‖ = 0 then 1 else Real.sin ‖v‖ / ‖v‖) * inner ℝ u v := by
      exact inner_exp_exp_eq u v hu hv;
    -- Recall that $1 - \|u-v\|^2/2 = 1 - (\|u\|^2 + \|v\|^2 - 2\langle u, v \rangle)/2 = (1 - \|u\|^2/2 - \|v\|^2/2) + \langle u, v \rangle$.
    have h_norm_eq : 1 - ‖u - v‖^2 / 2 = (1 - ‖u‖^2 / 2 - ‖v‖^2 / 2) + inner ℝ u v := by
      norm_num [ norm_sub_sq_real, hu, hv ] ; ring;
    -- Apply the triangle inequality to the expression.
    have h_triangle : |(Real.cos ‖u‖ * Real.cos ‖v‖ - (1 - ‖u‖^2 / 2 - ‖v‖^2 / 2)) + ((if ‖u‖ = 0 then 1 else Real.sin ‖u‖ / ‖u‖) * (if ‖v‖ = 0 then 1 else Real.sin ‖v‖ / ‖v‖) - 1) * inner ℝ u v| ≤ |Real.cos ‖u‖ * Real.cos ‖v‖ - (1 - ‖u‖^2 / 2 - ‖v‖^2 / 2)| + |((if ‖u‖ = 0 then 1 else Real.sin ‖u‖ / ‖u‖) * (if ‖v‖ = 0 then 1 else Real.sin ‖v‖ / ‖v‖) - 1) * inner ℝ u v| := by
      exact
        abs_add_le (Real.cos ‖u‖ * Real.cos ‖v‖ - (1 - ‖u‖ ^ 2 / 2 - ‖v‖ ^ 2 / 2))
          ((((if ‖u‖ = 0 then 1 else Real.sin ‖u‖ / ‖u‖) *
                if ‖v‖ = 0 then 1 else Real.sin ‖v‖ / ‖v‖) -
              1) *
            inner ℝ u v);
    convert h_triangle.trans ( add_le_add ( cos_mul_approx _ _ ( show |‖u‖| ≤ 1 by rw [ abs_of_nonneg ( norm_nonneg u ) ] ; exact hu_norm ) ( show |‖v‖| ≤ 1 by rw [ abs_of_nonneg ( norm_nonneg v ) ] ; exact hv_norm ) |> le_trans <| ?_ ) ( sinc_mul_approx _ _ hu_norm hv_norm ) ) using 1;
    · exact congr_arg _ ( by rw [ h_exp_inner, h_norm_eq ] ; ring );
    · norm_num [ abs_of_nonneg, add_nonneg, sq_nonneg, mul_nonneg ];
      exact le_abs_self _

/-
For $x \in [0, 1]$, $|\arccos(x)^2 - 2(1-x)| \le C(1-x)^2$.
-/
