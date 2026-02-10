/-
Logits, embeddings, and bridge theorem (head-level).

This file defines the scalar logits used by GSM attention and by standard
dot-product attention, plus the per-head probability matrices. It also
collects the head-level statements for SI Theorems S4–S8.

Notation: throughout, Q and K map token indices into R^3, which are embedded
as pure imaginary quaternions using `pure_quaternion`. The GSM logits use the
geodesic distance on Spin(3) (via `d_geo`) between the corresponding rotors
`exp(Q)` and `exp(K)`.
-/
import Mathlib
import RgatPaperProofs.Geometry
import RgatPaperProofs.Attention.Softmax

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 800000
set_option maxRecDepth 6000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-
### Quaternion embedding

We embed a 3-vector `v` into the pure imaginary quaternion `0 + v`.
This aligns with the SI convention that the rotor manifold uses unit quaternions
with zero real part for tangent directions.
-/

def pure_quaternion (v : Fin 3 → ℝ) : Quaternion ℝ :=
  ⟨0, v 0, v 1, v 2⟩

/-
### Logits (SI Eq. S4/S5)

`gsm_logits` is the geodesic distance based logit from the SI: the squared
geodesic distance between the rotors `exp(Q i)` and `exp(K j)`, scaled by
`-1/(2 tau)`. `std_logits` is the usual dot-product logit scaled by `1/tau`.
-/
noncomputable def gsm_logits {T : ℕ} (Q K : Fin T → Fin 3 → ℝ) (tau : ℝ) (i j : Fin T) : ℝ :=
  - (1 / (2 * tau)) * (d_geo (NormedSpace.exp ℝ (pure_quaternion (Q i))) (NormedSpace.exp ℝ (pure_quaternion (K j))))^2

noncomputable def std_logits {T : ℕ} (Q K : Fin T → Fin 3 → ℝ) (tau : ℝ) (i j : Fin T) : ℝ :=
  (1 / tau) * (∑ k : Fin 3, Q i k * K j k)

/-
### Probability matrices

`P_gsm` and `P_std` are the row-wise softmaxes of the corresponding logits.
Each row is a probability distribution over keys.
-/
noncomputable def P_gsm {T : ℕ} (Q K : Fin T → Fin 3 → ℝ) (tau : ℝ) (i : Fin T) : Fin T → ℝ :=
  softmax (gsm_logits Q K tau i)

noncomputable def P_std {T : ℕ} (Q K : Fin T → Fin 3 → ℝ) (tau : ℝ) (i : Fin T) : Fin T → ℝ :=
  softmax (std_logits Q K tau i)

/-
Sanity check: a trivial theorem to confirm the file builds.
-/
theorem test_true : True := True.intro

/-
### SI Theorem S4 (Head-level bridge bound)

This statement is the per-head small-angle bound comparing GSM and standard
attention probabilities. It is used as a building block for stack-level bounds
in later modules.
-/
def BridgeTheoremHeadStatement : Prop :=
  ∀ (tau_min : ℝ), tau_min > 0 →
  ∃ C_head > 0, ∀ ε > 0, ε < 1 →
  ∀ (T : ℕ) [NeZero T] (Q K : Fin T → Fin 3 → ℝ) (tau : ℝ),
  tau ≥ tau_min →
  (∀ i, ‖pure_quaternion (Q i)‖ ≤ ε) →
  (∀ j, ‖pure_quaternion (K j)‖ ≤ ε) →
  norm_infty_2 (fun i => P_gsm Q K tau i - P_std Q K tau i) ≤ C_head * ε^2

/-
### SI Theorem S5 (Markov diffusion operator)

Each row of `P_gsm` is nonnegative, sums to 1, and the output is in the convex
hull of the values. This is the algebraic "stochastic matrix" property used for
non-expansive and truncation bounds.
-/
def TheoremS5Statement : Prop :=
  ∀ (T d : ℕ) [NeZero T] (Q K : Fin T → Fin 3 → ℝ) (tau : ℝ) (v : Fin T → Fin d → ℝ),
  (∀ i j, 0 ≤ P_gsm Q K tau i j) ∧
  (∀ i, ∑ j, P_gsm Q K tau i j = 1) ∧
  (∀ i, (∑ j, P_gsm Q K tau i j • v j) ∈ convexHull ℝ (Set.range v))

/-
Weighted output (context mix) for attention.

This is the standard attention output for a fixed row `i` of the weight matrix
`P`.
-/
noncomputable def weighted_output {T d : ℕ} (P : Fin T → Fin T → ℝ) (v : Fin T → Fin d → ℝ) (i : Fin T) : Fin d → ℝ :=
  ∑ j, P i j • v j

/-
### SI Corollary S6 (Non-expansive bounds)

If the values are uniformly bounded, then the attention output is uniformly
bounded, and the map `v ↦ weighted_output P v` is 1-Lipschitz in the `∞`-norm.
-/
def CorollaryS6Statement : Prop :=
  ∀ (T d : ℕ) [NeZero T] (P : Fin T → Fin T → ℝ) (v v' : Fin T → Fin d → ℝ) (V_max : ℝ),
  (∀ i j, 0 ≤ P i j) →
  (∀ i, ∑ j, P i j = 1) →
  (∀ j, ‖v j‖ ≤ V_max) →
  (∀ i, ‖weighted_output P v i‖ ≤ V_max) ∧
  (∀ i, ‖weighted_output P v i - weighted_output P v' i‖ ≤ norm_infty (fun j => ‖v j - v' j‖))

/-
### SI Lemma S7 (Exact truncation identity)

This identity expresses the difference between the full attention output and
the truncated output in terms of the mass of the omitted keys.
-/
def LemmaS7Statement : Prop :=
  ∀ (T d : ℕ) [NeZero T] (P : Fin T → Fin T → ℝ) (v : Fin T → Fin d → ℝ) (S : Fin T → Finset (Fin T)) (i : Fin T),
  let p_i := ∑ j ∈ S i, P i j
  let delta_i := 1 - p_i
  let mu_S := (1 / p_i) • ∑ j ∈ S i, P i j • v j
  let mu_Sc := (1 / delta_i) • ∑ j ∈ (Finset.univ \ S i), P i j • v j
  let y_i := ∑ j, P i j • v j
  let y_tilde_i := mu_S
  (∑ j, P i j = 1) →
  (p_i ≠ 0 → delta_i ≠ 0 → y_i - y_tilde_i = delta_i • (mu_Sc - mu_S))

/-
### SI Corollary S8 (Truncation bound)

With bounded values, the truncation error scales linearly with the omitted mass
`delta_i`.
-/
def CorollaryS8Statement : Prop :=
  ∀ (T d : ℕ) [NeZero T] (P : Fin T → Fin T → ℝ) (v : Fin T → Fin d → ℝ) (S : Fin T → Finset (Fin T)) (i : Fin T) (V_max : ℝ),
  let p_i := ∑ j ∈ S i, P i j
  let delta_i := 1 - p_i
  let mu_S := (1 / p_i) • ∑ j ∈ S i, P i j • v j
  let y_i := ∑ j, P i j • v j
  let y_tilde_i := mu_S
  (∀ j, ‖v j‖ ≤ V_max) →
  (∑ j, P i j = 1) →
  (∀ j, 0 ≤ P i j) →
  (p_i ≠ 0 → ‖y_i - y_tilde_i‖ ≤ 2 * V_max * delta_i)

/-
### Softmax stability

This is the `1/2`-Lipschitz bound for softmax under the `∞`-norm, used in the
bridge theorem bound.
-/
lemma softmax_stability {n : ℕ} [NeZero n] (x y : Fin n → ℝ) :
  norm_infty (softmax x - softmax y) ≤ (1 / 2) * norm_infty (x - y) := by
    refine' norm_infty_le _ _;
    · intro i;
      -- Mean value theorem on f(t) = softmax(x + t(y - x)).
      have h_mean_value :
          ∃ c ∈ Set.Icc (0 : ℝ) 1,
            (softmax y i - softmax x i) = deriv (fun t => softmax (x + t • (y - x)) i) c := by
        have := exists_deriv_eq_slope (f := fun t => softmax (x + t • (y - x)) i) zero_lt_one;
        exact this (Continuous.continuousOn <| by
          exact Differentiable.continuous <| by
            exact differentiable_softmax_line_segment _ _ _)
          (Differentiable.differentiableOn <| by
            exact differentiable_softmax_line_segment _ _ _) |>
          fun ⟨c, hc₁, hc₂⟩ =>
            ⟨c, ⟨hc₁.1.le, hc₁.2.le⟩, by
              norm_num at *; linarith⟩;
      have h_deriv_bound :
          ∀ c ∈ Set.Icc (0 : ℝ) 1,
            |deriv (fun t => softmax (x + t • (y - x)) i) c| ≤
              1 / 2 * norm_infty (y - x) := by
        intros c hc
        have h_deriv_bound :
            |deriv (fun t => softmax (x + t • (y - x)) i) c| ≤
              ∑ j, |(y j - x j) *
                (softmax (x + c • (y - x)) i *
                  ((if i = j then 1 else 0) - softmax (x + c • (y - x)) j))| := by
          have h_deriv_bound :
              deriv (fun t => softmax (x + t • (y - x)) i) c =
                ∑ j, (y j - x j) *
                  (softmax (x + c • (y - x)) i *
                    ((if i = j then 1 else 0) - softmax (x + c • (y - x)) j)) := by
            convert deriv_softmax_line_segment _ _ _ _ using 1;
            infer_instance;
          exact h_deriv_bound ▸ Finset.abs_sum_le_sum_abs _ _;
        have h_deriv_bound :
            ∑ j, |(y j - x j) *
              (softmax (x + c • (y - x)) i *
                ((if i = j then 1 else 0) - softmax (x + c • (y - x)) j))| ≤
              norm_infty (y - x) *
                ∑ j, |softmax (x + c • (y - x)) i *
                  ((if i = j then 1 else 0) - softmax (x + c • (y - x)) j)| := by
          rw [Finset.mul_sum _ _ _];
          exact Finset.sum_le_sum fun j _ => by
            rw [abs_mul];
            exact mul_le_mul_of_nonneg_right (norm_infty_ge_abs (y - x) j) (abs_nonneg _);
        have h_deriv_bound :
            ∑ j, |softmax (x + c • (y - x)) i *
              ((if i = j then 1 else 0) - softmax (x + c • (y - x)) j)| ≤ 1 / 2 := by
          convert softmax_jacobian_bound (x + c • (y - x)) i using 1;
        nlinarith [norm_infty_nonneg (y - x)];
      simp_all +decide [norm_infty, abs_sub_comm];
      exact abs_sub_le_iff.mpr ⟨
        by
          obtain ⟨c, hc₁, hc₂⟩ := h_mean_value;
          linarith [abs_le.mp (h_deriv_bound c hc₁.1 hc₁.2)],
        by
          obtain ⟨c, hc₁, hc₂⟩ := h_mean_value;
          linarith [abs_le.mp (h_deriv_bound c hc₁.1 hc₁.2)]⟩;
    · exact mul_nonneg (by norm_num) (norm_infty_nonneg _)

/-
Softmax is invariant under adding a constant to all components.

This is used to simplify expressions by shifting logits.
-/
lemma softmax_shift_invariant {n : ℕ} (x : Fin n → ℝ) (c : ℝ) :
  softmax (fun i => x i + c) = softmax x := by
    unfold softmax at *; ext i;
    simp +decide [Real.exp_add, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul];
    rw [← Finset.mul_sum _ _ _, mul_div_mul_left _ _ (ne_of_gt (Real.exp_pos _))]

/-
### GSM logits approximation (SI small-angle expansion)

When the embedded vectors are small, the squared geodesic distance between
rotors matches the squared Euclidean distance of the corresponding pure
quaternions up to higher-order terms.
-/
lemma logits_approx :
  ∀ (tau_min : ℝ), tau_min > 0 →
  ∃ C > 0, ∀ ε > 0, ε < 1 →
  ∀ (T : ℕ) [NeZero T] (Q K : Fin T → Fin 3 → ℝ) (tau : ℝ),
  tau ≥ tau_min →
  (∀ i, ‖pure_quaternion (Q i)‖ ≤ ε) →
  (∀ j, ‖pure_quaternion (K j)‖ ≤ ε) →
  ∀ i j, |gsm_logits Q K tau i j - (- (2 / tau) * ‖pure_quaternion (Q i) - pure_quaternion (K j)‖^2)| ≤ C * ε^4 := by
    intro tau_min htau_min
    have h_geo_bound :
        ∃ C_geo > 0, ∀ ε > 0, ε < 1 →
          ∀ (u v : Quaternion ℝ), u.re = 0 → v.re = 0 →
            ‖u‖ ≤ ε → ‖v‖ ≤ ε →
              |(d_geo (NormedSpace.exp ℝ u) (NormedSpace.exp ℝ v)) ^ 2 - 4 * ‖u - v‖ ^ 2| ≤
                C_geo * ε ^ 4 := by
      exact small_angle_expansion;
    obtain ⟨C_geo, hC_geo_pos, hC_geo⟩ := h_geo_bound;
    have htau_min_pos : 0 < tau_min := htau_min
    have hpos_C : 0 < C_geo / (2 * tau_min) := by
      have hden : 0 < 2 * tau_min := by nlinarith [htau_min_pos]
      exact div_pos hC_geo_pos hden
    refine' ⟨C_geo / (2 * tau_min), hpos_C, fun ε hε₁ hε₂ T _ Q K tau htau hQ hK i j => _⟩;
    have h_bound :
        |(d_geo (NormedSpace.exp ℝ (pure_quaternion (Q i)))
            (NormedSpace.exp ℝ (pure_quaternion (K j)))) ^ 2 -
          4 * ‖pure_quaternion (Q i) - pure_quaternion (K j)‖ ^ 2| ≤
        C_geo * ε ^ 4 := by
      exact hC_geo ε hε₁ hε₂ _ _ (by exact rfl) (by exact rfl) (hQ i) (hK j);
    have htau_pos : 0 < tau := lt_of_lt_of_le htau_min htau
    have h_inv_le : (1 / tau) ≤ (1 / tau_min) := by
      exact one_div_le_one_div_of_le htau_min htau
    unfold gsm_logits
    have h_scale :
        |-(1 / (2 * tau)) * (d_geo (NormedSpace.exp ℝ (pure_quaternion (Q i)))
            (NormedSpace.exp ℝ (pure_quaternion (K j))) ^ 2 -
          4 * ‖pure_quaternion (Q i) - pure_quaternion (K j)‖ ^ 2)|
          ≤ (1 / (2 * tau)) * (C_geo * ε ^ 4) := by
      have h_nonneg : 0 ≤ (1 / (2 * tau)) := by
        have hden : 0 ≤ (2 * tau) := by
          exact mul_nonneg (by norm_num) (le_of_lt htau_pos)
        exact one_div_nonneg.mpr hden
      have h_abs_tau : |1 / (2 * tau)| = (1 / (2 * tau)) := by
        exact abs_of_nonneg h_nonneg
      have h_mul := mul_le_mul_of_nonneg_left h_bound h_nonneg
      have h_eq :
          |-(1 / (2 * tau)) *
              (d_geo (NormedSpace.exp ℝ (pure_quaternion (Q i)))
                (NormedSpace.exp ℝ (pure_quaternion (K j))) ^ 2 -
                4 * ‖pure_quaternion (Q i) - pure_quaternion (K j)‖ ^ 2)| =
            (1 / (2 * tau)) *
              |d_geo (NormedSpace.exp ℝ (pure_quaternion (Q i)))
                  (NormedSpace.exp ℝ (pure_quaternion (K j))) ^ 2 -
                4 * ‖pure_quaternion (Q i) - pure_quaternion (K j)‖ ^ 2| := by
        calc
          |-(1 / (2 * tau)) *
              (d_geo (NormedSpace.exp ℝ (pure_quaternion (Q i)))
                (NormedSpace.exp ℝ (pure_quaternion (K j))) ^ 2 -
                4 * ‖pure_quaternion (Q i) - pure_quaternion (K j)‖ ^ 2)| =
          |(1 / (2 * tau)) *
                  (d_geo (NormedSpace.exp ℝ (pure_quaternion (Q i)))
                    (NormedSpace.exp ℝ (pure_quaternion (K j))) ^ 2 -
                    4 * ‖pure_quaternion (Q i) - pure_quaternion (K j)‖ ^ 2)| := by
            simpa using
              (abs_neg ((1 / (2 * tau)) *
                (d_geo (NormedSpace.exp ℝ (pure_quaternion (Q i)))
                  (NormedSpace.exp ℝ (pure_quaternion (K j))) ^ 2 -
                  4 * ‖pure_quaternion (Q i) - pure_quaternion (K j)‖ ^ 2)))
          _ = |1 / (2 * tau)| *
              |d_geo (NormedSpace.exp ℝ (pure_quaternion (Q i)))
                  (NormedSpace.exp ℝ (pure_quaternion (K j))) ^ 2 -
                4 * ‖pure_quaternion (Q i) - pure_quaternion (K j)‖ ^ 2| := by
            simpa using
              (abs_mul (1 / (2 * tau))
                (d_geo (NormedSpace.exp ℝ (pure_quaternion (Q i)))
                  (NormedSpace.exp ℝ (pure_quaternion (K j))) ^ 2 -
                  4 * ‖pure_quaternion (Q i) - pure_quaternion (K j)‖ ^ 2))
          _ = (1 / (2 * tau)) *
              |d_geo (NormedSpace.exp ℝ (pure_quaternion (Q i)))
                  (NormedSpace.exp ℝ (pure_quaternion (K j))) ^ 2 -
                4 * ‖pure_quaternion (Q i) - pure_quaternion (K j)‖ ^ 2| := by
            rw [h_abs_tau]
      calc
        |-(1 / (2 * tau)) *
            (d_geo (NormedSpace.exp ℝ (pure_quaternion (Q i)))
              (NormedSpace.exp ℝ (pure_quaternion (K j))) ^ 2 -
              4 * ‖pure_quaternion (Q i) - pure_quaternion (K j)‖ ^ 2)| =
            (1 / (2 * tau)) *
              |d_geo (NormedSpace.exp ℝ (pure_quaternion (Q i)))
                  (NormedSpace.exp ℝ (pure_quaternion (K j))) ^ 2 -
                4 * ‖pure_quaternion (Q i) - pure_quaternion (K j)‖ ^ 2| := by
          exact h_eq
        _ ≤ (1 / (2 * tau)) * (C_geo * ε ^ 4) := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using h_mul
    have h_scale' :
        (1 / (2 * tau)) * (C_geo * ε ^ 4) ≤ (C_geo / (2 * tau_min)) * ε ^ 4 := by
      have h_inv_le' : (1 / (2 * tau)) ≤ (1 / (2 * tau_min)) := by
        have hpos : 0 < (2 * tau_min) := by nlinarith [htau_min]
        have hle : (2 * tau_min) ≤ (2 * tau) := by nlinarith [htau]
        exact one_div_le_one_div_of_le hpos hle
      have h_nonneg : 0 ≤ C_geo * ε ^ 4 := by positivity
      have h_mul := mul_le_mul_of_nonneg_right h_inv_le' h_nonneg
      calc
        (1 / (2 * tau)) * (C_geo * ε ^ 4) ≤ (1 / (2 * tau_min)) * (C_geo * ε ^ 4) := h_mul
        _ = (C_geo / (2 * tau_min)) * ε ^ 4 := by ring
    have h_final :
        |-(1 / (2 * tau)) *
            (d_geo (NormedSpace.exp ℝ (pure_quaternion (Q i)))
              (NormedSpace.exp ℝ (pure_quaternion (K j))) ^ 2 -
              4 * ‖pure_quaternion (Q i) - pure_quaternion (K j)‖ ^ 2)|
          ≤ (C_geo / (2 * tau_min)) * ε ^ 4 := by
      exact h_scale.trans h_scale'
    have h_rewrite' :
        -(1 / (2 * tau)) *
            (d_geo (NormedSpace.exp ℝ (pure_quaternion (Q i)))
              (NormedSpace.exp ℝ (pure_quaternion (K j))) ^ 2 -
              4 * ‖pure_quaternion (Q i) - pure_quaternion (K j)‖ ^ 2) =
          -(1 / (2 * tau)) *
              d_geo (NormedSpace.exp ℝ (pure_quaternion (Q i)))
                (NormedSpace.exp ℝ (pure_quaternion (K j))) ^ 2 -
            -(2 / tau) * ‖pure_quaternion (Q i) - pure_quaternion (K j)‖ ^ 2 := by
      ring
    exact le_of_eq_of_le (congrArg abs (id (Eq.symm h_rewrite'))) h_final

/-
Properties of the pure quaternion embedding: squared norm and inner product preservation.
-/
lemma pure_quaternion_properties (u v : Fin 3 → ℝ) :
  ‖pure_quaternion u‖^2 = ∑ i, (u i)^2 ∧
  inner ℝ (pure_quaternion u) (pure_quaternion v) = ∑ i, u i * v i := by
    unfold pure_quaternion;
    norm_num [Norm.norm, Fin.sum_univ_three, inner];
    norm_num [Norm.norm, sq];
    rw [← sq, norm_eq_sqrt_real_inner]; norm_num [Quaternion.inner_self]; ring_nf;
    norm_num [Quaternion.normSq]; ring

/-
Standard logits expressed as inner product of pure quaternions.
-/
lemma std_logits_eq_inner {T : ℕ} (Q K : Fin T → Fin 3 → ℝ) (tau : ℝ) (i j : Fin T) :
  std_logits Q K tau i j =
    (1 / tau) * inner ℝ (pure_quaternion (Q i)) (pure_quaternion (K j)) := by
    unfold std_logits;
    unfold inner pure_quaternion;
    simp +decide [Quaternion.instInnerReal, Fin.sum_univ_three]

/-
Squared Euclidean distance between pure quaternions in terms of component sums.
-/
lemma pure_quaternion_dist_sq (u v : Fin 3 → ℝ) :
  ‖pure_quaternion u - pure_quaternion v‖^2 =
    ∑ i, (u i)^2 + ∑ i, (v i)^2 - 2 * ∑ i, u i * v i := by
    convert pure_quaternion_properties (u - v) (u - v) |> And.left using 1;
    norm_num [Fin.sum_univ_three]; ring_nf;
    · exact congr_arg Norm.norm (by ext <;> simp +decide [pure_quaternion]);
    · simpa [sub_sq, Finset.sum_add_distrib, Finset.mul_sum _ _ _] using by ring_nf;

/-
Expansion of the quadratic approximation of GSM logits in terms of norms and standard logits.
-/
lemma logits_expansion {T : ℕ} (Q K : Fin T → Fin 3 → ℝ) (tau : ℝ) (i j : Fin T) :
  - (2 / tau) * ‖pure_quaternion (Q i) - pure_quaternion (K j)‖^2 =
    - (2 / tau) * ‖pure_quaternion (Q i)‖^2 -
      (2 / tau) * ‖pure_quaternion (K j)‖^2 + 4 * std_logits Q K tau i j := by
    rw [show std_logits Q K tau i j =
      (1 / tau) * inner ℝ (pure_quaternion (Q i)) (pure_quaternion (K j))
      from std_logits_eq_inner Q K tau i j];
    rw [show ‖pure_quaternion (Q i) - pure_quaternion (K j)‖ ^ 2 =
        ‖pure_quaternion (Q i)‖ ^ 2 + ‖pure_quaternion (K j)‖ ^ 2 -
          2 * inner ℝ (pure_quaternion (Q i)) (pure_quaternion (K j)) by
        rw [@norm_sub_sq ℝ]; ring!];
    ring

/-
Theorem S4: The difference between GSM attention and standard attention is bounded by O(ε^2).
-/
theorem bridge_theorem_head : BridgeTheoremHeadStatement := by
  intro tau_min htau_min
  have h_diff :
      ∃ C > 0, ∀ ε > 0, ε < 1 → ∀ (T : ℕ) [NeZero T]
        (Q K : Fin T → Fin 3 → ℝ) (tau : ℝ),
        tau ≥ tau_min →
        (∀ i, ‖pure_quaternion (Q i)‖ ≤ ε) →
        (∀ j, ‖pure_quaternion (K j)‖ ≤ ε) →
        norm_infty_2 (fun i => P_gsm Q K tau i - P_std Q K tau i) ≤
          (1 / 2) * (norm_infty (fun i => norm_infty (fun j => gsm_logits Q K tau i j - std_logits Q K tau i j))) := by
    refine' ⟨1, by norm_num, _⟩;
    intros ε hε_pos hε_lt_1 T _ Q K tau htau hQ hK;
    have h_softmax_stability :
        ∀ x y : Fin T → ℝ, norm_infty (softmax x - softmax y) ≤ (1 / 2) * norm_infty (x - y) := by
      exact fun x y => softmax_stability x y;
    have h_row_stability :
        ∀ i, norm_infty (P_gsm Q K tau i - P_std Q K tau i) ≤
          (1 / 2) * norm_infty (fun j => gsm_logits Q K tau i j - std_logits Q K tau i j) := by
      exact fun i => h_softmax_stability (gsm_logits Q K tau i) (std_logits Q K tau i);
    refine' norm_infty_le ?_ ?_;
    · intro i
      have h_row :
          norm_l2 (P_gsm Q K tau i - P_std Q K tau i) ≤
            norm_infty (P_gsm Q K tau i - P_std Q K tau i) := by
        simpa using (norm_le_norm_infty (P_gsm Q K tau i - P_std Q K tau i))
      have h_row' :
          norm_l2 (P_gsm Q K tau i - P_std Q K tau i) ≤
            (1 / 2) * norm_infty (fun j => gsm_logits Q K tau i j - std_logits Q K tau i j) := by
        refine h_row.trans (h_row_stability i)
      have h_row'' :
          |norm_l2 (P_gsm Q K tau i - P_std Q K tau i)| ≤
            (1 / 2) * norm_infty (fun j => gsm_logits Q K tau i j - std_logits Q K tau i j) := by
        simpa [abs_of_nonneg (norm_l2_nonneg _)] using h_row'
      refine h_row''.trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      convert norm_infty_ge_abs _ i using 1
      rw [abs_of_nonneg (norm_infty_nonneg _)]
    · exact mul_nonneg (by norm_num) (norm_infty_nonneg _)
  obtain ⟨C, hC_pos, hC_bound⟩ := h_diff
  have h_diff_bound :
      ∃ C' > 0, ∀ ε > 0, ε < 1 → ∀ (T : ℕ) [NeZero T]
        (Q K : Fin T → Fin 3 → ℝ) (tau : ℝ),
        tau ≥ tau_min →
        (∀ i, ‖pure_quaternion (Q i)‖ ≤ ε) →
        (∀ j, ‖pure_quaternion (K j)‖ ≤ ε) →
        norm_infty (fun i => norm_infty (fun j => gsm_logits Q K tau i j - std_logits Q K tau i j)) ≤ C' * ε^2 := by
    have h_diff_bound :
        ∃ C' > 0, ∀ ε > 0, ε < 1 → ∀ (T : ℕ) [NeZero T]
          (Q K : Fin T → Fin 3 → ℝ) (tau : ℝ),
          tau ≥ tau_min →
          (∀ i, ‖pure_quaternion (Q i)‖ ≤ ε) →
          (∀ j, ‖pure_quaternion (K j)‖ ≤ ε) →
          ∀ i j, |gsm_logits Q K tau i j - std_logits Q K tau i j| ≤ C' * ε^2 := by
      have h_diff_bound :
          ∃ C' > 0, ∀ ε > 0, ε < 1 → ∀ (T : ℕ) [NeZero T]
            (Q K : Fin T → Fin 3 → ℝ) (tau : ℝ),
            tau ≥ tau_min →
            (∀ i, ‖pure_quaternion (Q i)‖ ≤ ε) →
            (∀ j, ‖pure_quaternion (K j)‖ ≤ ε) →
            ∀ i j,
              |gsm_logits Q K tau i j -
                (- (2 / tau) * ‖pure_quaternion (Q i)‖^2 -
                  (2 / tau) * ‖pure_quaternion (K j)‖^2 +
                    4 * std_logits Q K tau i j)| ≤ C' * ε^4 := by
        obtain ⟨C', hC'_pos, hC'_bound⟩ := logits_approx tau_min htau_min;
        exact ⟨C', hC'_pos, fun ε hε₁ hε₂ T _ Q K tau htau hQ hK i j => by
          convert hC'_bound ε hε₁ hε₂ T Q K tau htau hQ hK i j using 1;
          rw [logits_expansion Q K tau i j]⟩;
      obtain ⟨C', hC'_pos, hC'_bound⟩ := h_diff_bound;
      have hpos : 0 < (8 / tau_min) := by
        have hden : 0 < tau_min := htau_min
        exact div_pos (by norm_num) hden
      have hpos' : 0 < (8 / tau_min) + C' := by nlinarith [hpos, hC'_pos]
      refine' ⟨(8 / tau_min) + C', hpos', fun ε hε₁ hε₂ T _ Q K tau htau hQ hK i j => _⟩;
      have h_triangle :
          |gsm_logits Q K tau i j - std_logits Q K tau i j| ≤
            |gsm_logits Q K tau i j -
              (- (2 / tau) * ‖pure_quaternion (Q i)‖^2 -
                (2 / tau) * ‖pure_quaternion (K j)‖^2 +
                  4 * std_logits Q K tau i j)| +
            |(- (2 / tau) * ‖pure_quaternion (Q i)‖^2 -
                (2 / tau) * ‖pure_quaternion (K j)‖^2 +
                  4 * std_logits Q K tau i j) - std_logits Q K tau i j| := by
        exact abs_sub_le _ _ _;
      refine le_trans h_triangle <|
        le_trans (add_le_add (hC'_bound ε hε₁ hε₂ T Q K tau htau hQ hK i j)
          (show |(- (2 / tau) * ‖pure_quaternion (Q i)‖^2 -
              (2 / tau) * ‖pure_quaternion (K j)‖^2 +
                4 * std_logits Q K tau i j) - std_logits Q K tau i j| ≤ (8 / tau_min) * ε ^ 2 from ?_)) ?_;
      · have h_norm_bounds :
          ‖pure_quaternion (Q i)‖^2 ≤ ε^2 ∧
            ‖pure_quaternion (K j)‖^2 ≤ ε^2 ∧
              |std_logits Q K tau i j| ≤ (1 / tau_min) * ε^2 := by
          refine' ⟨pow_le_pow_left₀ (norm_nonneg _) (hQ i) 2,
            pow_le_pow_left₀ (norm_nonneg _) (hK j) 2, _⟩;
          have h_inner_bound :
              |inner ℝ (pure_quaternion (Q i)) (pure_quaternion (K j))| ≤ ε^2 := by
            have h_inner_bound :
                |inner ℝ (pure_quaternion (Q i)) (pure_quaternion (K j))| ≤
                  ‖pure_quaternion (Q i)‖ * ‖pure_quaternion (K j)‖ := by
              exact abs_real_inner_le_norm _ _;
            exact h_inner_bound.trans (by
              nlinarith only [hQ i, hK j, norm_nonneg (pure_quaternion (Q i)),
                norm_nonneg (pure_quaternion (K j))]);
          have htau_pos : 0 < tau := lt_of_lt_of_le htau_min htau
          have h_nonneg : 0 ≤ (1 / tau) := by
            exact one_div_nonneg.mpr (le_of_lt htau_pos)
          have h_abs :
              |(1 / tau) * inner ℝ (pure_quaternion (Q i)) (pure_quaternion (K j))|
                ≤ (1 / tau) * ε^2 := by
            have h_abs_tau : |1 / tau| = (1 / tau) := by
              exact abs_of_nonneg h_nonneg
            have h_mul := mul_le_mul_of_nonneg_left h_inner_bound h_nonneg
            calc
              |(1 / tau) * inner ℝ (pure_quaternion (Q i)) (pure_quaternion (K j))| =
                  |1 / tau| * |inner ℝ (pure_quaternion (Q i)) (pure_quaternion (K j))| := by
                simpa using
                  (abs_mul (1 / tau) (inner ℝ (pure_quaternion (Q i)) (pure_quaternion (K j))))
              _ = (1 / tau) * |inner ℝ (pure_quaternion (Q i)) (pure_quaternion (K j))| := by
                rw [h_abs_tau]
              _ ≤ (1 / tau) * ε^2 := by
                simpa [mul_comm, mul_left_comm, mul_assoc] using h_mul
          have h_inv_le : (1 / tau) ≤ (1 / tau_min) := by
            exact one_div_le_one_div_of_le htau_min htau
          have h_abs' :
              |(1 / tau) * inner ℝ (pure_quaternion (Q i)) (pure_quaternion (K j))|
                ≤ (1 / tau_min) * ε^2 := by
            exact h_abs.trans (mul_le_mul_of_nonneg_right h_inv_le (by nlinarith [hε₁]))
          simpa [std_logits_eq_inner] using h_abs'
        have hA :
            |-(2 / tau) * ‖pure_quaternion (Q i)‖^2| ≤ (2 / tau_min) * ε^2 := by
          have htau_pos : 0 < tau := lt_of_lt_of_le htau_min htau
          have h_nonneg : 0 ≤ (2 / tau) := by
            have hden : 0 ≤ (1 / tau) := one_div_nonneg.mpr (le_of_lt htau_pos)
            have htwo : 0 ≤ (2 : ℝ) := by norm_num
            simpa [div_eq_mul_inv] using mul_nonneg htwo hden
          have h_abs_tau : |2 / tau| = (2 / tau) := by
            exact abs_of_nonneg h_nonneg
          have h_abs :
              |(2 / tau) * ‖pure_quaternion (Q i)‖^2| ≤ (2 / tau) * ε^2 := by
            simpa [abs_mul, h_abs_tau, mul_comm, mul_left_comm, mul_assoc] using
              (mul_le_mul_of_nonneg_left h_norm_bounds.1 h_nonneg)
          have h_inv_le : (2 / tau) ≤ (2 / tau_min) := by
            calc
              2 / tau = 2 * (1 / tau) := by ring
              _ ≤ 2 * (1 / tau_min) := by
                nlinarith [one_div_le_one_div_of_le htau_min htau]
              _ = 2 / tau_min := by ring
          have h_abs' :
              |(2 / tau) * ‖pure_quaternion (Q i)‖^2| ≤ (2 / tau_min) * ε^2 := by
            exact h_abs.trans (mul_le_mul_of_nonneg_right h_inv_le (by nlinarith [hε₁]))
          simpa [abs_mul, h_abs_tau] using h_abs'
        have hB :
            |-(2 / tau) * ‖pure_quaternion (K j)‖^2| ≤ (2 / tau_min) * ε^2 := by
          have htau_pos : 0 < tau := lt_of_lt_of_le htau_min htau
          have h_nonneg : 0 ≤ (2 / tau) := by
            have hden : 0 ≤ (1 / tau) := one_div_nonneg.mpr (le_of_lt htau_pos)
            have htwo : 0 ≤ (2 : ℝ) := by norm_num
            simpa [div_eq_mul_inv] using mul_nonneg htwo hden
          have h_abs_tau : |2 / tau| = (2 / tau) := by
            exact abs_of_nonneg h_nonneg
          have h_abs :
              |(2 / tau) * ‖pure_quaternion (K j)‖^2| ≤ (2 / tau) * ε^2 := by
            simpa [abs_mul, h_abs_tau, mul_comm, mul_left_comm, mul_assoc] using
              (mul_le_mul_of_nonneg_left h_norm_bounds.2.1 h_nonneg)
          have h_inv_le : (2 / tau) ≤ (2 / tau_min) := by
            calc
              2 / tau = 2 * (1 / tau) := by ring
              _ ≤ 2 * (1 / tau_min) := by
                nlinarith [one_div_le_one_div_of_le htau_min htau]
              _ = 2 / tau_min := by ring
          have h_abs' :
              |(2 / tau) * ‖pure_quaternion (K j)‖^2| ≤ (2 / tau_min) * ε^2 := by
            exact h_abs.trans (mul_le_mul_of_nonneg_right h_inv_le (by nlinarith [hε₁]))
          simpa [abs_mul, h_abs_tau] using h_abs'
        have hC :
            |3 * std_logits Q K tau i j| ≤ (3 / tau_min) * ε^2 := by
          have h_abs_3 : |(3 : ℝ)| = 3 := by
            exact abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)
          calc
            |3 * std_logits Q K tau i j| = 3 * |std_logits Q K tau i j| := by
              simp [abs_mul, h_abs_3, mul_comm, mul_left_comm, mul_assoc]
            _ ≤ 3 * ((1 / tau_min) * ε^2) := by
              exact mul_le_mul_of_nonneg_left h_norm_bounds.2.2 (by norm_num)
            _ = (3 / tau_min) * ε^2 := by ring
        have hAB :
            |-(2 / tau) * ‖pure_quaternion (Q i)‖^2 -
                (2 / tau) * ‖pure_quaternion (K j)‖^2| ≤ (4 / tau_min) * ε^2 := by
          have h_triangle :
              |-(2 / tau) * ‖pure_quaternion (Q i)‖^2 -
                  (2 / tau) * ‖pure_quaternion (K j)‖^2| ≤
                |2 / tau| * ‖pure_quaternion (Q i)‖^2 +
                  |2 / tau| * ‖pure_quaternion (K j)‖^2 := by
            have hQ_nonneg : 0 ≤ ‖pure_quaternion (Q i)‖^2 := by
              nlinarith [sq_nonneg (‖pure_quaternion (Q i)‖)]
            have hK_nonneg : 0 ≤ ‖pure_quaternion (K j)‖^2 := by
              nlinarith [sq_nonneg (‖pure_quaternion (K j)‖)]
            have h_triangle' :
                |-(2 / tau * ‖pure_quaternion (Q i)‖^2) +
                    -(2 / tau * ‖pure_quaternion (K j)‖^2)| ≤
                  |-(2 / tau * ‖pure_quaternion (Q i)‖^2)| +
                    |-(2 / tau * ‖pure_quaternion (K j)‖^2)| :=
              abs_add_le (-(2 / tau * ‖pure_quaternion (Q i)‖^2))
                (-(2 / tau * ‖pure_quaternion (K j)‖^2))
            have hAabs :
                |-(2 / tau * ‖pure_quaternion (Q i)‖^2)| =
                  |2 / tau| * ‖pure_quaternion (Q i)‖^2 := by
              simp [abs_mul, abs_neg, abs_of_nonneg hQ_nonneg, mul_comm, mul_left_comm, mul_assoc]
            have hBabs :
                |-(2 / tau * ‖pure_quaternion (K j)‖^2)| =
                  |2 / tau| * ‖pure_quaternion (K j)‖^2 := by
              simp [abs_mul, abs_neg, abs_of_nonneg hK_nonneg, mul_comm, mul_left_comm, mul_assoc]
            have h_triangle'' :
                |-(2 / tau * ‖pure_quaternion (Q i)‖^2) +
                    -(2 / tau * ‖pure_quaternion (K j)‖^2)| ≤
                  |2 / tau| * ‖pure_quaternion (Q i)‖^2 +
                    |2 / tau| * ‖pure_quaternion (K j)‖^2 := by
              simpa [hAabs, hBabs] using h_triangle'
            simpa [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using h_triangle''
          have hA' :
              |2 / tau| * ‖pure_quaternion (Q i)‖^2 ≤ (2 / tau_min) * ε^2 := by
            have hQ_nonneg : 0 ≤ ‖pure_quaternion (Q i)‖^2 := by
              nlinarith [sq_nonneg (‖pure_quaternion (Q i)‖)]
            calc
              |2 / tau| * ‖pure_quaternion (Q i)‖^2 =
              |2 / tau| * |‖pure_quaternion (Q i)‖^2| := by
                    simp [abs_of_nonneg hQ_nonneg]
              _ = |(2 / tau) * ‖pure_quaternion (Q i)‖^2| := by
                    simpa using (abs_mul (2 / tau) (‖pure_quaternion (Q i)‖^2))
              _ = |-(2 / tau) * ‖pure_quaternion (Q i)‖^2| := by
                    simpa using (abs_neg ((2 / tau) * ‖pure_quaternion (Q i)‖^2))
              _ ≤ (2 / tau_min) * ε^2 := hA
          have hB' :
              |2 / tau| * ‖pure_quaternion (K j)‖^2 ≤ (2 / tau_min) * ε^2 := by
            have hK_nonneg : 0 ≤ ‖pure_quaternion (K j)‖^2 := by
              nlinarith [sq_nonneg (‖pure_quaternion (K j)‖)]
            calc
              |2 / tau| * ‖pure_quaternion (K j)‖^2 =
              |2 / tau| * |‖pure_quaternion (K j)‖^2| := by
                    simp [abs_of_nonneg hK_nonneg]
              _ = |(2 / tau) * ‖pure_quaternion (K j)‖^2| := by
                    simpa using (abs_mul (2 / tau) (‖pure_quaternion (K j)‖^2))
              _ = |-(2 / tau) * ‖pure_quaternion (K j)‖^2| := by
                    simpa using (abs_neg ((2 / tau) * ‖pure_quaternion (K j)‖^2))
              _ ≤ (2 / tau_min) * ε^2 := hB
          have h_sum :
              |2 / tau| * ‖pure_quaternion (Q i)‖^2 +
                |2 / tau| * ‖pure_quaternion (K j)‖^2 ≤
              (2 / tau_min) * ε^2 + (2 / tau_min) * ε^2 := by
            exact add_le_add hA' hB'
          have h_sum' :
              (2 / tau_min) * ε^2 + (2 / tau_min) * ε^2 = (4 / tau_min) * ε^2 := by
            ring
          exact h_triangle.trans (h_sum.trans_eq h_sum')
        have hABC :
            |-(2 / tau) * ‖pure_quaternion (Q i)‖^2 -
                (2 / tau) * ‖pure_quaternion (K j)‖^2 +
                  3 * std_logits Q K tau i j| ≤ (7 / tau_min) * ε^2 := by
          have h_triangle :
              |-(2 / tau) * ‖pure_quaternion (Q i)‖^2 -
                  (2 / tau) * ‖pure_quaternion (K j)‖^2 +
                    3 * std_logits Q K tau i j| ≤
                |-(2 / tau) * ‖pure_quaternion (Q i)‖^2 -
                    (2 / tau) * ‖pure_quaternion (K j)‖^2| +
                  |3 * std_logits Q K tau i j| := by
            have h_triangle' :
                |( -(2 / tau * ‖pure_quaternion (Q i)‖^2) +
                    -(2 / tau * ‖pure_quaternion (K j)‖^2)) +
                    3 * std_logits Q K tau i j| ≤
                  |-(2 / tau * ‖pure_quaternion (Q i)‖^2) +
                      -(2 / tau * ‖pure_quaternion (K j)‖^2)| +
                    |3 * std_logits Q K tau i j| :=
              abs_add_le
                (-(2 / tau * ‖pure_quaternion (Q i)‖^2) +
                  -(2 / tau * ‖pure_quaternion (K j)‖^2))
                (3 * std_logits Q K tau i j)
            simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
              mul_comm, mul_left_comm, mul_assoc] using h_triangle'
          have h_sum : |-(2 / tau) * ‖pure_quaternion (Q i)‖^2 -
                (2 / tau) * ‖pure_quaternion (K j)‖^2| +
              |3 * std_logits Q K tau i j| ≤
              (4 / tau_min) * ε^2 + (3 / tau_min) * ε^2 := by
            exact add_le_add hAB hC
          have h_sum' :
              (4 / tau_min) * ε^2 + (3 / tau_min) * ε^2 = (7 / tau_min) * ε^2 := by
            ring
          exact h_triangle.trans (h_sum.trans_eq h_sum')
        have h_rewrite :
            (- (2 / tau) * ‖pure_quaternion (Q i)‖^2 -
                (2 / tau) * ‖pure_quaternion (K j)‖^2 +
                  4 * std_logits Q K tau i j) - std_logits Q K tau i j =
              -(2 / tau) * ‖pure_quaternion (Q i)‖^2 -
                (2 / tau) * ‖pure_quaternion (K j)‖^2 +
                  3 * std_logits Q K tau i j := by
          ring
        have h_final :
            |(- (2 / tau) * ‖pure_quaternion (Q i)‖^2 -
                (2 / tau) * ‖pure_quaternion (K j)‖^2 +
                  4 * std_logits Q K tau i j) - std_logits Q K tau i j| ≤
              (8 / tau_min) * ε^2 := by
          have h_nonneg : 0 ≤ (1 / tau_min) * ε^2 := by
            have hτ : 0 ≤ (1 / tau_min) := by
              exact one_div_nonneg.mpr (le_of_lt htau_min)
            have hε : 0 ≤ ε^2 := by nlinarith
            exact mul_nonneg hτ hε
          have h_le :
              (7 / tau_min) * ε^2 ≤ (8 / tau_min) * ε^2 := by
            calc
              (7 / tau_min) * ε^2 = 7 * ((1 / tau_min) * ε^2) := by ring
              _ ≤ 8 * ((1 / tau_min) * ε^2) := by
                exact mul_le_mul_of_nonneg_right (by norm_num : (7 : ℝ) ≤ 8) h_nonneg
              _ = (8 / tau_min) * ε^2 := by ring
          have h' :
              |(- (2 / tau) * ‖pure_quaternion (Q i)‖^2 -
                  (2 / tau) * ‖pure_quaternion (K j)‖^2 +
                    4 * std_logits Q K tau i j) - std_logits Q K tau i j| ≤
                (7 / tau_min) * ε^2 := by
            convert hABC using 1
            ring_nf
          exact h'.trans h_le
        exact h_final
      · nlinarith [show 0 ≤ C' * ε ^ 2 by positivity, show ε ^ 2 ≤ 1 by nlinarith, htau_min];
    obtain ⟨C', hC'_pos, hC'_bound⟩ := h_diff_bound;
    use C';
    refine' ⟨hC'_pos, fun ε hε_pos hε_lt_1 T hT Q K tau htau hQ hK => _⟩;
    refine' norm_infty_le _ _;
    · intro i;
      rw [abs_of_nonneg];
      · refine' norm_infty_le _ _;
        · exact fun j => hC'_bound ε hε_pos hε_lt_1 T Q K tau htau hQ hK i j;
        · positivity;
      · exact le_trans (abs_nonneg _) (norm_infty_ge_abs _ ⟨0, hT.pos⟩);
    · positivity;
  exact ⟨h_diff_bound.choose / 2, half_pos h_diff_bound.choose_spec.1,
    fun ε hε₁ hε₂ T hT Q K tau htau hQ hK =>
      le_trans (hC_bound ε hε₁ hε₂ T Q K tau htau hQ hK)
        (mul_le_mul_of_nonneg_left (h_diff_bound.choose_spec.2 ε hε₁ hε₂ T Q K tau htau hQ hK)
          (by norm_num)) |>
        le_trans <| by nlinarith [h_diff_bound.choose_spec.1]⟩
