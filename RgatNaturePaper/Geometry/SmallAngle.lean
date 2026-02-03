/-
Small-angle expansions for geodesic distance.

Provides bounds that relate `arccos` and the squared geodesic distance to
Euclidean quantities in the small-angle regime.
-/
import Mathlib
import RgatNaturePaper.Geometry.Basic
import RgatNaturePaper.Geometry.ExpApprox

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
Key arccosine quadratic approximation used in S4/S5 expansions.
-/

lemma arccos_sq_approx :
  ∃ C > 0, ∀ x : ℝ, 0 ≤ x → x ≤ 1 → |Real.arccos x ^ 2 - 2 * (1 - x)| ≤ C * (1 - x) ^ 2 := by
    -- Let's choose the constant $C = 16$.
    use 166; norm_num;
    -- Let $x = \cos \theta$ with $\theta \in [0, \pi/2]$.
    intro x hx_nonneg hx_le_one
    set θ : ℝ := Real.arccos x
    have hθ_range : 0 ≤ θ ∧ θ ≤ Real.pi / 2 := by
      exact ⟨ Real.arccos_nonneg _, by rw [ Real.arccos_le_pi_div_two ] ; linarith ⟩;
    -- We want $|\theta^2 - 4\sin^2(\theta/2)| \le C (2\sin^2(\theta/2))^2 = 4C \sin^4(\theta/2)$.
    suffices h_sin_approx : ∀ θ : ℝ, 0 ≤ θ ∧ θ ≤ Real.pi / 2 → |θ^2 - 4 * Real.sin (θ / 2)^2| ≤ 166 * (2 * Real.sin (θ / 2)^2)^2 by
      convert h_sin_approx θ hθ_range using 2 <;> norm_num [ Real.sin_sq, Real.cos_sq ] ; ring_nf;
      · rw [ Real.cos_arccos ] <;> linarith;
      · rw [ mul_div_cancel₀ _ two_ne_zero, Real.cos_arccos ] <;> linarith;
    -- For $\theta \in [0, \pi/2]$, we have $\sin(\theta/2) \leq \theta/2$ and $\sin(\theta/2) \geq \theta/2 - (\theta/2)^3 / 6$.
    have h_sin_bounds : ∀ θ : ℝ, 0 ≤ θ ∧ θ ≤ Real.pi / 2 → Real.sin (θ / 2) ≤ θ / 2 ∧ Real.sin (θ / 2) ≥ θ / 2 - (θ / 2)^3 / 6 := by
      intros θ hθ_range
      have h_sin_le : Real.sin (θ / 2) ≤ θ / 2 := by
        rcases eq_or_lt_of_le hθ_range.1 with ( rfl | hθ_pos ) <;> [ norm_num; exact le_of_lt ( Real.sin_lt <| by linarith ) ]
      have h_sin_ge : Real.sin (θ / 2) ≥ θ / 2 - (θ / 2)^3 / 6 := by
        -- Utilize the known inequality for the sine function: $\sin(x) \geq x - \frac{x^3}{6}$ for $0 \leq x \leq \frac{\pi}{2}$.
        have h_sin_ineq : ∀ x : ℝ, 0 ≤ x ∧ x ≤ Real.pi / 2 → Real.sin x ≥ x - x^3 / 6 := by
          -- Let's choose any $x \in [0, \frac{\pi}{2}]$ and derive the inequality.
          intro x hx_range
          have h_sin_deriv : ∀ t ∈ Set.Icc 0 x, Real.cos t ≥ 1 - t^2 / 2 := by
            exact fun t a ↦ Real.one_sub_sq_div_two_le_cos;
          -- Integrate both sides of $\cos t \geq 1 - t^2 / 2$ from $0$ to $x$.
          have h_integral : ∫ t in (0 : ℝ)..x, Real.cos t ≥ ∫ t in (0 : ℝ)..x, (1 - t^2 / 2) := by
            refine' intervalIntegral.integral_mono_on _ _ _ _ <;> aesop;
          norm_num at h_integral; linarith;
        grind
      exact ⟨h_sin_le, h_sin_ge⟩;
    intro θ hθ_range
    have h_sin_sq_bounds : Real.sin (θ / 2)^2 ≤ (θ / 2)^2 ∧ Real.sin (θ / 2)^2 ≥ (θ / 2 - (θ / 2)^3 / 6)^2 := by
      exact ⟨ pow_le_pow_left₀ ( Real.sin_nonneg_of_nonneg_of_le_pi ( by linarith ) ( by linarith ) ) ( h_sin_bounds θ hθ_range |>.1 ) 2, pow_le_pow_left₀ ( by nlinarith [ Real.pi_le_four, pow_nonneg hθ_range.1 2, pow_nonneg hθ_range.1 3 ] ) ( h_sin_bounds θ hθ_range |>.2 ) 2 ⟩;
    rw [ abs_le ] ; constructor <;> nlinarith [ pow_nonneg hθ_range.1 3, pow_nonneg hθ_range.1 4, pow_nonneg hθ_range.1 5, pow_nonneg hθ_range.1 6, Real.pi_le_four ] ;

/-
The deviation of the inner product from 1 is bounded by $O(\varepsilon^2)$.
-/
lemma inner_deviation_bound :
  ∃ C > 0, ∀ ε > 0, ε < 1 →
  ∀ u v : Quaternion ℝ, u.re = 0 → v.re = 0 → ‖u‖ ≤ ε → ‖v‖ ≤ ε →
  |1 - inner ℝ (NormedSpace.exp ℝ u) (NormedSpace.exp ℝ v)| ≤ C * ε ^ 2 := by
    -- We have `inner (exp u) (exp v) \approx 1 - ||u-v||^2/2`.
    have h_inner_approx : ∀ ε > 0, ε < 1 → ∀ u v : Quaternion ℝ, u.re = 0 → v.re = 0 → ‖u‖ ≤ ε → ‖v‖ ≤ ε → |inner ℝ (NormedSpace.exp ℝ u) (NormedSpace.exp ℝ v) - (1 - ‖u - v‖^2 / 2)| ≤ ε^4 + ε^4 + ε^4 / 2 + (ε^2 / 6 + ε^2 / 6 + ε^4 / 36) * ε^2 := by
      intros ε hε_pos hε_lt_1 u v hu hv hu_norm hv_norm
      have h_inner_approx : |inner ℝ (NormedSpace.exp ℝ u) (NormedSpace.exp ℝ v) - (1 - ‖u - v‖^2 / 2)| ≤ |‖u‖^4 + ‖v‖^4 + ‖u‖^2 * ‖v‖^2 / 2| + (‖u‖^2 / 6 + ‖v‖^2 / 6 + ‖u‖^2 * ‖v‖^2 / 36) * (‖u‖ * ‖v‖) := by
        convert inner_expansion_combine u v hu hv ( show ‖u‖ ≤ 1 by linarith ) ( show ‖v‖ ≤ 1 by linarith ) using 1;
      refine le_trans h_inner_approx ?_;
      refine' add_le_add _ _;
      · rw [ abs_of_nonneg ( by positivity ) ];
        nlinarith only [ show 0 ≤ ‖u‖ ^ 2 * ‖v‖ ^ 2 by positivity, show 0 ≤ ‖u‖ ^ 4 by positivity, show 0 ≤ ‖v‖ ^ 4 by positivity, show ‖u‖ ^ 2 ≤ ε ^ 2 by nlinarith only [ hu_norm, norm_nonneg u ], show ‖v‖ ^ 2 ≤ ε ^ 2 by nlinarith only [ hv_norm, norm_nonneg v ] ];
      · gcongr;
        · nlinarith only [ show 0 ≤ ‖u‖ * ‖v‖ by positivity, show ‖u‖ * ‖v‖ ≤ ε ^ 2 by nlinarith only [ norm_nonneg u, norm_nonneg v, hu_norm, hv_norm ], hu_norm, hv_norm ];
        · nlinarith [ norm_nonneg u, norm_nonneg v ];
    -- Since `||u-v|| \le ||u|| + ||v|| \le 2\epsilon`, `||u-v||^2/2 \le 2\epsilon^2`.
    have h_norm_diff : ∀ ε > 0, ε < 1 → ∀ u v : Quaternion ℝ, u.re = 0 → v.re = 0 → ‖u‖ ≤ ε → ‖v‖ ≤ ε → ‖u - v‖^2 / 2 ≤ 2 * ε^2 := by
      exact fun ε hε₁ hε₂ u v hu hv hu' hv' => by nlinarith [ norm_nonneg ( u - v ), show ‖u - v‖ ≤ ε + ε by exact le_trans ( norm_sub_le _ _ ) ( add_le_add hu' hv' ) ] ;
    refine' ⟨ 8 + 8 + 8 / 2 + ( 8 / 6 + 8 / 6 + 8 / 36 ) * 8, by norm_num, fun ε hε₁ hε₂ u v hu hv hu' hv' => _ ⟩;
    rw [ abs_sub_comm ];
    have := abs_le.mp ( h_inner_approx ε hε₁ hε₂ u v hu hv hu' hv' );
    cases abs_cases ( Inner.inner ℝ ( NormedSpace.exp ℝ u ) ( NormedSpace.exp ℝ v ) - 1 ) <;> nlinarith [ pow_pos hε₁ 3, pow_pos hε₁ 4, pow_pos hε₁ 5, pow_pos hε₁ 6, pow_pos hε₁ 7, pow_pos hε₁ 8, h_norm_diff ε hε₁ hε₂ u v hu hv hu' hv' ]

/-
The squared geodesic distance is approximately $8(1 - \langle q, k \rangle)$, with error $O(\varepsilon^4)$.
-/
lemma d_geo_sq_approx_linear :
  ∃ C > 0, ∀ ε > 0, ε < 1 →
  ∀ u v : Quaternion ℝ, u.re = 0 → v.re = 0 → ‖u‖ ≤ ε → ‖v‖ ≤ ε →
  |d_geo (NormedSpace.exp ℝ u) (NormedSpace.exp ℝ v) ^ 2 - 8 * (1 - inner ℝ (NormedSpace.exp ℝ u) (NormedSpace.exp ℝ v))| ≤ C * ε ^ 4 := by
    -- By combining the results from `arccos_sq_approx` and `inner_deviation_bound`, we can bound the deviation of the squared geodesic distance from $8(1 - \langle q, k \rangle)$.
    have h_combined : ∃ C > 0, ∀ ε > 0, ε < 1 → ∀ u v : Quaternion ℝ, u.re = 0 → v.re = 0 → ‖u‖ ≤ ε → ‖v‖ ≤ ε → |Real.arccos (abs (inner ℝ (NormedSpace.exp ℝ u) (NormedSpace.exp ℝ v))) ^ 2 - 2 * (1 - abs (inner ℝ (NormedSpace.exp ℝ u) (NormedSpace.exp ℝ v)))| ≤ C * ε ^ 4 := by
      -- Applying the bounds from `arccos_sq_approx` and `inner_deviation_bound`, we can bound the deviation of the squared geodesic distance from $8(1 - \langle q, k \rangle)$.
      obtain ⟨C₁, hC₁⟩ : ∃ C₁ > 0, ∀ x : ℝ, 0 ≤ x → x ≤ 1 → |Real.arccos x ^ 2 - 2 * (1 - x)| ≤ C₁ * (1 - x) ^ 2 := by
        exact arccos_sq_approx;
      -- Applying the bounds from `inner_deviation_bound`, we can bound the deviation of the inner product from 1.
      obtain ⟨C₂, hC₂⟩ : ∃ C₂ > 0, ∀ ε > 0, ε < 1 → ∀ u v : Quaternion ℝ, u.re = 0 → v.re = 0 → ‖u‖ ≤ ε → ‖v‖ ≤ ε → |1 - abs (inner ℝ (NormedSpace.exp ℝ u) (NormedSpace.exp ℝ v))| ≤ C₂ * ε ^ 2 := by
        -- Applying the bounds from `inner_deviation_bound`, we can bound the deviation of the inner product from 1. Since $|1 - x| \leq |1 - x|$ for any $x$, we can use the same constant $C₂$.
        obtain ⟨C₂, hC₂⟩ : ∃ C₂ > 0, ∀ ε > 0, ε < 1 → ∀ u v : Quaternion ℝ, u.re = 0 → v.re = 0 → ‖u‖ ≤ ε → ‖v‖ ≤ ε → |1 - inner ℝ (NormedSpace.exp ℝ u) (NormedSpace.exp ℝ v)| ≤ C₂ * ε ^ 2 := by
          exact inner_deviation_bound;
        refine' ⟨ C₂, hC₂.1, fun ε hε₁ hε₂ u v hu hv hu' hv' => _ ⟩;
        refine' le_trans _ ( hC₂.2 ε hε₁ hε₂ u v hu hv hu' hv' );
        cases abs_cases ( Inner.inner ℝ ( NormedSpace.exp ℝ u ) ( NormedSpace.exp ℝ v ) ) <;> cases abs_cases ( 1 - |Inner.inner ℝ ( NormedSpace.exp ℝ u ) ( NormedSpace.exp ℝ v )| ) <;> cases abs_cases ( 1 - Inner.inner ℝ ( NormedSpace.exp ℝ u ) ( NormedSpace.exp ℝ v ) ) <;> linarith;
      refine' ⟨ 8 * C₁ * C₂ ^ 2 + 1, by nlinarith, fun ε hε₁ hε₂ u v hu hv hu' hv' => _ ⟩;
      refine' le_trans ( hC₁.2 _ _ _ ) _;
      · positivity;
      · have h_inner_bound : ∀ u v : Quaternion ℝ, ‖u‖ = 1 → ‖v‖ = 1 → |inner ℝ u v| ≤ 1 := by
          exact fun u v hu hv => by simpa [ hu, hv ] using abs_real_inner_le_norm u v;
        convert h_inner_bound ( ‖NormedSpace.exp ℝ u‖⁻¹ • NormedSpace.exp ℝ u ) ( ‖NormedSpace.exp ℝ v‖⁻¹ • NormedSpace.exp ℝ v ) _ _ using 1 <;> norm_num [ norm_smul, hu, hv ];
      · -- Applying the bound from `inner_deviation_bound`, we get:
        have h_inner_bound : |1 - abs (inner ℝ (NormedSpace.exp ℝ u) (NormedSpace.exp ℝ v))| ≤ C₂ * ε ^ 2 := by
          exact hC₂.2 ε hε₁ hε₂ u v hu hv hu' hv';
        -- Squaring both sides of the inequality $|1 - |inner| \leq C₂ * ε²|$, we get $(1 - |inner|)^2 \leq (C₂ * ε²)^2$.
        have h_sq : (1 - abs (inner ℝ (NormedSpace.exp ℝ u) (NormedSpace.exp ℝ v)))^2 ≤ (C₂ * ε^2)^2 := by
          simpa [ sq_abs ] using pow_le_pow_left₀ ( abs_nonneg _ ) h_inner_bound 2;
        nlinarith [ show 0 ≤ C₁ * ε ^ 4 by exact mul_nonneg hC₁.1.le ( by positivity ) ];
    obtain ⟨ C, hC₀, hC ⟩ := h_combined;
    -- We need to show that $|8(1 - |x|) - 8(1 - x)| \le O(\varepsilon^4)$.
    have h_abs : ∃ C > 0, ∀ ε > 0, ε < 1 → ∀ u v : Quaternion ℝ, u.re = 0 → v.re = 0 → ‖u‖ ≤ ε → ‖v‖ ≤ ε → |8 * (1 - abs (inner ℝ (NormedSpace.exp ℝ u) (NormedSpace.exp ℝ v))) - 8 * (1 - inner ℝ (NormedSpace.exp ℝ u) (NormedSpace.exp ℝ v))| ≤ C * ε ^ 4 := by
      -- By `inner_deviation_bound`, $|1 - x| \le C \varepsilon^2$. So $(1-x)^2 \le C^2 \varepsilon^4$.
      obtain ⟨ C', hC'₀, hC' ⟩ : ∃ C' > 0, ∀ ε > 0, ε < 1 → ∀ u v : Quaternion ℝ, u.re = 0 → v.re = 0 → ‖u‖ ≤ ε → ‖v‖ ≤ ε → |1 - inner ℝ (NormedSpace.exp ℝ u) (NormedSpace.exp ℝ v)| ≤ C' * ε ^ 2 := by
        exact inner_deviation_bound;
      -- If $x \ge 0$, then $|x| = x$, so the LHS is zero.
      use 8 * C'^2;
      refine' ⟨ by positivity, fun ε hε₁ hε₂ u v hu hv hu' hv' => abs_le.mpr ⟨ _, _ ⟩ ⟩ <;> cases abs_cases ( Inner.inner ℝ ( NormedSpace.exp ℝ u ) ( NormedSpace.exp ℝ v ) ) <;> nlinarith [ abs_le.mp ( hC' ε hε₁ hε₂ u v hu hv hu' hv' ), show 0 ≤ C' * ε ^ 2 by positivity ];
    obtain ⟨ C', hC'₀, hC' ⟩ := h_abs;
    refine' ⟨ 8 * C + C', by positivity, fun ε hε₁ hε₂ u v hu hv hu' hv' => _ ⟩;
    unfold d_geo;
    unfold s_sim;
    exact abs_le.mpr ⟨ by nlinarith [ abs_le.mp ( hC ε hε₁ hε₂ u v hu hv hu' hv' ), abs_le.mp ( hC' ε hε₁ hε₂ u v hu hv hu' hv' ) ], by nlinarith [ abs_le.mp ( hC ε hε₁ hε₂ u v hu hv hu' hv' ), abs_le.mp ( hC' ε hε₁ hε₂ u v hu hv hu' hv' ) ] ⟩

/-
The inner product of exponentials is approximately $1 - \|u-v\|^2/2$ with error $O(\varepsilon^4)$.
-/
lemma inner_approx :
  ∃ C > 0, ∀ ε > 0, ε < 1 →
  ∀ u v : Quaternion ℝ, u.re = 0 → v.re = 0 → ‖u‖ ≤ ε → ‖v‖ ≤ ε →
  |inner ℝ (NormedSpace.exp ℝ u) (NormedSpace.exp ℝ v) - (1 - ‖u - v‖ ^ 2 / 2)| ≤ C * ε ^ 4 := by
    -- By combining the results from `inner_expansion_combine` and `inner_deviation_bound`, we get the desired inequality.
    use (8 : ℝ) + (1 : ℝ) + (1 : ℝ) + (1 : ℝ) + (1 : ℝ) + (1 : ℝ) + (1 : ℝ) + (1 : ℝ) + (1 : ℝ) + (1 : ℝ);
    refine' ⟨ by norm_num, fun ε hε₁ hε₂ u v hu hv hu' hv' => _ ⟩;
    refine' le_trans ( inner_expansion_combine u v hu hv ( hu'.trans hε₂.le ) ( hv'.trans hε₂.le ) ) _;
    refine' le_trans ( add_le_add ( show |‖u‖ ^ 4 + ‖v‖ ^ 4 + ‖u‖ ^ 2 * ‖v‖ ^ 2 / 2| ≤ ε ^ 4 + ε ^ 4 + ε ^ 2 * ε ^ 2 / 2 by rw [ abs_of_nonneg ( by positivity ) ] ; gcongr ) ( show ( ‖u‖ ^ 2 / 6 + ‖v‖ ^ 2 / 6 + ‖u‖ ^ 2 * ‖v‖ ^ 2 / 36 ) * ( ‖u‖ * ‖v‖ ) ≤ ( ε ^ 2 / 6 + ε ^ 2 / 6 + ε ^ 2 * ε ^ 2 / 36 ) * ( ε * ε ) by gcongr ) ) _;
    nlinarith [ pow_pos hε₁ 3, pow_pos hε₁ 4, pow_pos hε₁ 5, pow_pos hε₁ 6, pow_pos hε₁ 7, pow_pos hε₁ 8, pow_pos hε₁ 9, pow_pos hε₁ 10 ]

/-
Let $u,v\in\R^3$ with $\|u\|,\|v\|\le \varepsilon$ and $\varepsilon$ below the injectivity radius, and define $q=\exp(u)$, $k=\exp(v)$ in $\Spin(3)$. Then there exists $C>0$ (depending only on the Lie bracket constants) such that $|\dgeo(q,k)^2 - 4\|u-v\|^2| \le C\,\varepsilon^4$.
-/
lemma small_angle_expansion :
  ∃ C > 0, ∀ ε > 0, ε < 1 →
  ∀ u v : Quaternion ℝ, u.re = 0 → v.re = 0 → ‖u‖ ≤ ε → ‖v‖ ≤ ε →
  |d_geo (NormedSpace.exp ℝ u) (NormedSpace.exp ℝ v) ^ 2 - 4 * ‖u - v‖ ^ 2| ≤ C * ε ^ 4 := by
    -- By the triangle inequality:
    -- \[
    -- |\dgeo(q,k)^2 - 4\|u-v\|^2| \le |\dgeo(q,k)^2 - 8(1 - \text{inner})| + |8(1 - \text{inner}) - 4\|u-v\|^2|
    -- \]
    -- We already have bounds for both terms on the right-hand side.
    obtain ⟨C₁, hC₁⟩ := d_geo_sq_approx_linear;
    obtain ⟨C₂, hC₂⟩ := inner_approx;
    use C₁ + 8 * C₂;
    exact ⟨ by linarith, fun ε hε₁ hε₂ u v hu hv hu' hv' => abs_le.mpr ⟨ by linarith [ abs_le.mp ( hC₁.2 ε hε₁ hε₂ u v hu hv hu' hv' ), abs_le.mp ( hC₂.2 ε hε₁ hε₂ u v hu hv hu' hv' ) ], by linarith [ abs_le.mp ( hC₁.2 ε hε₁ hε₂ u v hu hv hu' hv' ), abs_le.mp ( hC₂.2 ε hε₁ hε₂ u v hu hv hu' hv' ) ] ⟩ ⟩

/-
Lemma S2 (Small-angle distance expansion).
This is a named alias for `small_angle_expansion`, matching the SI result.
-/
def LemmaS2Statement : Prop :=
  ∀ ε0 > 0, ∃ C > 0, ∀ ε > 0, ε ≤ ε0 → ε < 1 →
  ∀ u v : Quaternion ℝ, u.re = 0 → v.re = 0 → ‖u‖ ≤ ε → ‖v‖ ≤ ε →
  |d_geo (NormedSpace.exp ℝ u) (NormedSpace.exp ℝ v) ^ 2 - 4 * ‖u - v‖ ^ 2| ≤ C * ε ^ 4

theorem LemmaS2 : LemmaS2Statement := by
  intro ε0 hε0
  obtain ⟨C, hC⟩ := small_angle_expansion
  refine ⟨C, hC.1, ?_⟩
  intro ε hεpos hεle hεlt u v hu hv hu' hv'
  exact hC.2 ε hεpos hεlt u v hu hv hu' hv'
