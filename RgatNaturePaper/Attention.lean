/-
Module: Attention
-/
import Mathlib
import RgatNaturePaper.Geometry

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 300000
set_option maxRecDepth 3000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-
The sum of softmax components is 1 for non-empty vectors.
-/
noncomputable def softmax {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => Real.exp (x i) / ∑ j, Real.exp (x j)

lemma softmax_sum_one {n : ℕ} [NeZero n] (x : Fin n → ℝ) : ∑ i, softmax x i = 1 := by
  unfold softmax;
  rw [ ← Finset.sum_div, div_self <| ne_of_gt <| Finset.sum_pos ( fun _ _ => Real.exp_pos _ ) Finset.univ_nonempty ]

/-
The sum of exponentials is positive.
-/
lemma sum_exp_pos {n : ℕ} [NeZero n] (x : Fin n → ℝ) : 0 < ∑ j, Real.exp (x j) := by
  exact Finset.sum_pos ( fun _ _ => Real.exp_pos _ ) Finset.univ_nonempty

/-
The partial derivative of the sum of exponentials with respect to $x_j$ is $e^{x_j}$.
-/
lemma sum_exp_deriv {n : ℕ} (x : Fin n → ℝ) (j : Fin n) :
  fderiv ℝ (fun y => ∑ k, Real.exp (y k)) x (Pi.single j 1) = Real.exp (x j) := by
    -- The derivative of the sum of exponentials with respect to $x_j$ is $e^{x_j}$.
    have h_deriv_sum : ∀ (x : Fin n → ℝ), fderivWithin ℝ (fun y : Fin n → ℝ => ∑ k, Real.exp (y k)) Set.univ x = (fun v : Fin n → ℝ => ∑ k, Real.exp (x k) * v k) := by
      intro x;
      ext v;
      rw [ fderivWithin_univ, HasFDerivAt.fderiv ];
      rotate_right;
      exact ∑ k, ContinuousLinearMap.smulRight ( ContinuousLinearMap.proj k ) ( Real.exp ( x k ) );
      · simp +decide [mul_comm];
      · convert HasFDerivAt.sum fun i _ => HasFDerivAt.exp ( hasFDerivAt_apply i x ) using 1;
        any_goals exact Finset.univ;
        · ext v; simp +decide [mul_comm];
        · exact Finset.sum_congr rfl fun _ _ => by ext; simp +decide [mul_comm];
    convert congr_arg ( fun f => f ( Pi.single j 1 ) ) ( h_deriv_sum x ) using 1 ; aesop;
    simp +decide [ Pi.single_apply ]

/-
The partial derivative of $e^{x_i}$ with respect to $x_j$ is $\delta_{ij} e^{x_i}$.
-/
lemma exp_deriv_apply {n : ℕ} (x : Fin n → ℝ) (i j : Fin n) :
  fderiv ℝ (fun y => Real.exp (y i)) x (Pi.single j 1) = (if i = j then Real.exp (x i) else 0) := by
    erw [ fderiv_exp ] <;> norm_num;
    · erw [ HasFDerivAt.fderiv ( hasFDerivAt_apply _ _ ) ] ; aesop;
    · exact differentiableAt_pi.1 differentiableAt_id _

/-
Definition of the infinity norm for a vector in $\mathbb{R}^n$.
-/
noncomputable def norm_infty {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  (Finset.univ.image (fun i => |x i|)).max.getD 0

/-
Checking if softmax is defined.
-/
#check softmax

/-
Embedding of R^3 into pure imaginary quaternions.
-/
def pure_quaternion (v : Fin 3 → ℝ) : Quaternion ℝ :=
  ⟨0, v 0, v 1, v 2⟩

/-
Definitions of GSM logits and standard logits.
-/
noncomputable def gsm_logits {T : ℕ} (Q K : Fin T → Fin 3 → ℝ) (tau : ℝ) (i j : Fin T) : ℝ :=
  - (1 / (2 * tau)) * (d_geo (NormedSpace.exp ℝ (pure_quaternion (Q i))) (NormedSpace.exp ℝ (pure_quaternion (K j))))^2

noncomputable def std_logits {T : ℕ} (Q K : Fin T → Fin 3 → ℝ) (tau : ℝ) (i j : Fin T) : ℝ :=
  (1 / tau) * (∑ k : Fin 3, Q i k * K j k)

/-
Definitions of GSM and standard attention probability matrices.
-/
noncomputable def P_gsm {T : ℕ} (Q K : Fin T → Fin 3 → ℝ) (tau : ℝ) (i : Fin T) : Fin T → ℝ :=
  softmax (gsm_logits Q K tau i)

noncomputable def P_std {T : ℕ} (Q K : Fin T → Fin 3 → ℝ) (tau : ℝ) (i : Fin T) : Fin T → ℝ :=
  softmax (std_logits Q K tau i)

/-
Test theorem with complete proof.
-/
theorem test_true : True := True.intro

/-
Statement of Theorem S4 (Bridge Theorem, head-level bound).
-/
def BridgeTheoremHeadStatement : Prop :=
  ∃ C_head > 0, ∀ ε > 0, ε < 1 →
  ∀ (T : ℕ) [NeZero T] (Q K : Fin T → Fin 3 → ℝ) (tau : ℝ),
  tau ≥ 1 →
  (∀ i, ‖pure_quaternion (Q i)‖ ≤ ε) →
  (∀ j, ‖pure_quaternion (K j)‖ ≤ ε) →
  norm_infty (fun i => norm_infty (P_gsm Q K tau i - P_std Q K tau i)) ≤ C_head * ε^2

/-
Theorem S5: GSM attention is a Markov diffusion operator. Each row of P is a probability distribution, and the output lies in the convex hull of the values.
-/
def TheoremS5Statement : Prop :=
  ∀ (T : ℕ) [NeZero T] (Q K : Fin T → Fin 3 → ℝ) (tau : ℝ) (v : Fin T → Fin 3 → ℝ),
  (∀ i j, 0 ≤ P_gsm Q K tau i j) ∧
  (∀ i, ∑ j, P_gsm Q K tau i j = 1) ∧
  (∀ i, (∑ j, P_gsm Q K tau i j • v j) ∈ convexHull ℝ (Set.range v))

/-
Definition of the weighted output (context mix) for attention.
-/
noncomputable def weighted_output {T d : ℕ} (P : Fin T → Fin T → ℝ) (v : Fin T → Fin d → ℝ) (i : Fin T) : Fin d → ℝ :=
  ∑ j, P i j • v j

/-
Corollary S6: Non-expansive bounds. If values are bounded, the output is bounded, and the operation is non-expansive with respect to values.
-/
def CorollaryS6Statement : Prop :=
  ∀ (T d : ℕ) [NeZero T] (P : Fin T → Fin T → ℝ) (v v' : Fin T → Fin d → ℝ) (V_max : ℝ),
  (∀ i j, 0 ≤ P i j) →
  (∀ i, ∑ j, P i j = 1) →
  (∀ j, ‖v j‖ ≤ V_max) →
  (∀ i, ‖weighted_output P v i‖ ≤ V_max) ∧
  (∀ i, ‖weighted_output P v i - weighted_output P v' i‖ ≤ norm_infty (fun j => ‖v j - v' j‖))

/-
Lemma S7: Exact truncation identity. y_i - tilde{y}_i = delta_i (mu_{S^c} - mu_S).
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
Corollary S8: Truncation bound. If values are bounded, the truncation error is bounded by 2 * V_max * delta_i.
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
