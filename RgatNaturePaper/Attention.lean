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

/- The partial derivative of the i-th component of the softmax function w.r.t. j-th input. -/
lemma softmax_deriv {n : ℕ} (x : Fin n → ℝ) (i j : Fin n) :
  fderiv ℝ (fun y => softmax y i) x (Pi.single j 1) =
    softmax x i * ((if i = j then 1 else 0) - softmax x j) := by
  unfold softmax
  have h_exp : DifferentiableAt ℝ (fun y : Fin n → ℝ => Real.exp (y i)) x := by
    fun_prop
  have h_sum : DifferentiableAt ℝ (fun y : Fin n → ℝ => ∑ j, Real.exp (y j)) x := by
    fun_prop (disch := norm_num)
  erw [fderiv_mul] <;> norm_num [h_exp, h_sum,
    ne_of_gt (show 0 < ∑ j : Fin n, Real.exp (x j) from
      Finset.sum_pos (fun _ _ => Real.exp_pos _) ⟨j, Finset.mem_univ _⟩)]
  erw [fderiv_comp x
    (show DifferentiableAt ℝ (fun y : ℝ => y⁻¹) (∑ j : Fin n, Real.exp (x j)) from
      DifferentiableAt.inv differentiableAt_id
        (ne_of_gt <| Finset.sum_pos (fun _ _ => Real.exp_pos _) ⟨j, Finset.mem_univ _⟩))] <;>
    norm_num [h_exp, h_sum,
      ne_of_gt (show 0 < ∑ j : Fin n, Real.exp (x j) from
        Finset.sum_pos (fun _ _ => Real.exp_pos _) ⟨j, Finset.mem_univ _⟩)]
  erw [fderiv_exp] <;> norm_num [h_exp, h_sum]
  · have h_deriv_sum :
      (fderiv ℝ (fun y => ∑ j, Real.exp (y j)) x) (Pi.single j 1) = Real.exp (x j) := by
      simpa using (sum_exp_deriv x j)
    have h_deriv_exp :
        (fderiv ℝ (fun y => y i) x) (Pi.single j 1) = if i = j then 1 else 0 := by
      erw [HasFDerivAt.fderiv (hasFDerivAt_apply _ _)] ; aesop
    rw [h_deriv_sum, h_deriv_exp] ; ring
  · exact differentiableAt_pi.1 differentiableAt_id i

/- The infinity norm dominates the absolute value of any component. -/
lemma norm_infty_ge_abs {n : ℕ} (x : Fin n → ℝ) (i : Fin n) : |x i| ≤ norm_infty x := by
  have h_le_max : ∀ i, |x i| ≤ Finset.max (Finset.image (fun i => |x i|) Finset.univ) := by
    exact fun i => Finset.le_max (Finset.mem_image_of_mem _ (Finset.mem_univ _))
  have h_max_eq_norm_infty :
      Finset.max (Finset.image (fun i => |x i|) Finset.univ) = norm_infty x := by
    unfold norm_infty
    cases h : Finset.max (Finset.image (fun i => |x i|) Finset.univ) <;> aesop
  exact_mod_cast h_max_eq_norm_infty ▸ h_le_max i

/- The infinity norm is non-negative. -/
lemma norm_infty_nonneg {n : ℕ} (x : Fin n → ℝ) : 0 ≤ norm_infty x := by
  have h_nonneg : ∀ x : Fin n → ℝ, 0 ≤ norm_infty x := by
    intro x; exact (by
      have h_nonneg : ∀ x : Fin n → ℝ, 0 ≤ norm_infty x := by
        intro x
        have h_abs_nonneg : ∀ i, 0 ≤ |x i| := by
          norm_num +zetaDelta at *
        have h_max_nonneg : ∀ {s : Finset ℝ}, (∀ y ∈ s, 0 ≤ y) → 0 ≤ s.max.getD 0 := by
          intros s hs_nonneg; induction' s using Finset.induction with y s ih; aesop; (
          simp_all +decide [ Finset.max ];
          cases max_cases ( y : WithBot ℝ ) ( s.sup WithBot.some ) <;> aesop)
        exact h_max_nonneg fun y hy => by
          obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
          exact h_abs_nonneg i
      exact h_nonneg x)
  exact h_nonneg x

/- The directional derivative of the softmax function in the direction v. -/
lemma softmax_directional_deriv {n : ℕ} (x v : Fin n → ℝ) (i : Fin n) :
  fderiv ℝ (fun y => softmax y i) x v =
    ∑ j, v j * (softmax x i * ((if i = j then 1 else 0) - softmax x j)) := by
  have h_def :
      (fderiv ℝ (fun y => softmax y i) x) v =
        ∑ j, (fderiv ℝ (fun y => softmax y i) x) (Pi.single j 1) * v j := by
    rw [show v = ∑ j, Pi.single j (v j) by ext j; simp +decide [Pi.single_apply]]
    simp +decide [mul_comm, Finset.mul_sum _ _ _]
    exact Finset.sum_congr rfl fun j _ => by
      rw [← smul_eq_mul, ← ContinuousLinearMap.map_smul]
      congr
      ext k; by_cases hk : k = j <;> aesop
  exact h_def.trans (Finset.sum_congr rfl fun j _ => by rw [softmax_deriv] ; ring)

/- The infinity norm of the Jacobian of softmax is bounded by 1/2. -/
lemma softmax_jacobian_bound {n : ℕ} [NeZero n] (x : Fin n → ℝ) :
  ∀ i, ∑ j, |softmax x i * ((if i = j then 1 else 0) - softmax x j)| ≤ 1 / 2 := by
  intro i
  have h_factor :
      ∑ j, |softmax x i * ((if i = j then 1 else 0) - softmax x j)| =
        |softmax x i| * ∑ j, |(if i = j then 1 else 0) - softmax x j| := by
    rw [Finset.mul_sum _ _ _, Finset.sum_congr rfl fun _ _ => abs_mul _ _]
  have h_split :
      ∑ j, |(if i = j then 1 else 0) - softmax x j| =
        |1 - softmax x i| + ∑ j ∈ Finset.univ.erase i, |softmax x j| := by
    rw [Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ i)]
    rw [Finset.sdiff_singleton_eq_erase]
    exact congrArg₂ _ (by simp +decide) (Finset.sum_congr rfl fun j hj => by aesop)
  have h_bounds :
      |1 - softmax x i| ≤ 1 ∧ ∑ j ∈ Finset.univ.erase i, |softmax x j| ≤ 1 - softmax x i := by
    have h_bounds : ∀ j, 0 ≤ softmax x j ∧ softmax x j ≤ 1 := by
      exact fun j =>
        ⟨div_nonneg (Real.exp_nonneg _) (Finset.sum_nonneg fun _ _ => Real.exp_nonneg _),
          div_le_one_of_le₀
            (Finset.single_le_sum (fun i _ => Real.exp_nonneg (x i)) (Finset.mem_univ j))
            (Finset.sum_nonneg fun _ _ => Real.exp_nonneg _)⟩
    refine ⟨?_, ?_⟩
    · exact abs_le.mpr ⟨by linarith [h_bounds i], by linarith [h_bounds i]⟩
    · rw [Finset.sum_congr rfl fun j hj => abs_of_nonneg (h_bounds j |>.1)]
      rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
      linarith [h_bounds i, show ∑ j, softmax x j = 1 from softmax_sum_one x]
  cases abs_cases (softmax x i) <;> cases abs_cases (1 - softmax x i) <;>
    nlinarith [sq_nonneg (softmax x i - 1 / 2),
      show 0 ≤ softmax x i from
        div_nonneg (Real.exp_nonneg _) (Finset.sum_nonneg fun _ _ => Real.exp_nonneg _),
      show 0 ≤ ∑ j ∈ Finset.univ.erase i, |softmax x j| from
        Finset.sum_nonneg fun _ _ => abs_nonneg _]

/- Line segment in ℝ^n between l and l'. -/
def line_segment {n : ℕ} (l l' : Fin n → ℝ) (t : ℝ) : Fin n → ℝ :=
  l + t • (l' - l)

lemma differentiable_line_segment {n : ℕ} (l l' : Fin n → ℝ) :
  Differentiable ℝ (line_segment l l') := by
  exact differentiable_pi.mpr fun i =>
    Differentiable.add (differentiable_const _) (Differentiable.mul differentiable_id (differentiable_const _))

lemma differentiable_softmax_line_segment {n : ℕ} (l l' : Fin n → ℝ) (i : Fin n) :
  Differentiable ℝ (fun t => softmax (line_segment l l' t) i) := by
  unfold softmax line_segment
  refine' Differentiable.div _ _ _ <;> norm_num [Real.differentiable_exp, mul_comm]
  exact fun x => ne_of_gt <| Finset.sum_pos (fun _ _ => Real.exp_pos _) ⟨i, Finset.mem_univ _⟩

lemma deriv_softmax_line_segment {n : ℕ} [NeZero n] (l l' : Fin n → ℝ) (i : Fin n) (c : ℝ) :
  deriv (fun t => softmax (line_segment l l' t) i) c =
    ∑ j, (l' j - l j) *
      (softmax (line_segment l l' c) i * ((if i = j then 1 else 0) - softmax (line_segment l l' c) j)) := by
  convert (HasDerivAt.deriv _) using 1
  have h_chain :
      HasDerivAt (fun t => softmax (line_segment l l' t) i)
        (∑ j, (l' j - l j) * (softmax (line_segment l l' c) i *
          ((if i = j then 1 else 0) - softmax (line_segment l l' c) j))) c := by
    have h_inner : HasDerivAt (fun t => line_segment l l' t) (l' - l) c := by
      rw [hasDerivAt_pi]
      exact fun i => by
        simpa using
          HasDerivAt.add (hasDerivAt_const _ _) (HasDerivAt.mul (hasDerivAt_id c) (hasDerivAt_const _ _))
    have h_outer : DifferentiableAt ℝ (fun y => softmax y i) (line_segment l l' c) := by
      have h_outer : DifferentiableAt ℝ (fun y => Real.exp (y i)) (line_segment l l' c) := by
        fun_prop (disch := solve_by_elim)
      have h_outer : DifferentiableAt ℝ (fun y => ∑ j, Real.exp (y j)) (line_segment l l' c) := by
        fun_prop (disch := norm_num)
      exact DifferentiableAt.mul (by assumption)
        (h_outer.inv (ne_of_gt (Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty)))
    convert HasFDerivAt.hasDerivAt (h_outer.hasFDerivAt.comp c h_inner.hasFDerivAt) using 1
    convert (softmax_directional_deriv (line_segment l l' c) (l' - l) i) |> Eq.symm using 1
    norm_num
  simpa only [mul_assoc, mul_comm, mul_left_comm] using h_chain

/- If every component is bounded by C, then norm_infty ≤ C. -/
lemma norm_infty_le {n : ℕ} {x : Fin n → ℝ} {C : ℝ} (h : ∀ i, |x i| ≤ C) (hC : 0 ≤ C) :
  norm_infty x ≤ C := by
  rcases n with (_ | _ | n) <;> simp_all +decide [Fin.forall_fin_succ]
  · unfold norm_infty; aesop
  · unfold norm_infty; aesop
  · have h_max_le_C : ∀ i : Fin (Nat.succ (Nat.succ n)), |x i| ≤ C := by
      rintro (_ | _ | i) <;> simp +arith +decide [*]
      exact h.2.2 ⟨i, by linarith⟩
    have h_max_le_C :
        Finset.max (Finset.image (fun i => |x i|) Finset.univ) ≤ C := by
      exact Finset.max_le fun x hx => by
        rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
        exact WithBot.coe_le_coe.mpr (h_max_le_C i)
    norm_num [norm_infty]
    cases h : Finset.max (Finset.image (fun i => |x i|) Finset.univ) <;> aesop

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

/-
The softmax function is Lipschitz continuous with constant 1/2 with respect to the infinity norm.
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
-/
lemma softmax_shift_invariant {n : ℕ} (x : Fin n → ℝ) (c : ℝ) :
  softmax (fun i => x i + c) = softmax x := by
    unfold softmax at *; ext i;
    simp +decide [Real.exp_add, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul];
    rw [← Finset.mul_sum _ _ _, mul_div_mul_left _ _ (ne_of_gt (Real.exp_pos _))]

/-
The GSM logits are approximately proportional to the squared Euclidean distance between the quaternions.
-/
lemma logits_approx :
  ∃ C > 0, ∀ ε > 0, ε < 1 →
  ∀ (T : ℕ) [NeZero T] (Q K : Fin T → Fin 3 → ℝ) (tau : ℝ),
  tau ≥ 1 →
  (∀ i, ‖pure_quaternion (Q i)‖ ≤ ε) →
  (∀ j, ‖pure_quaternion (K j)‖ ≤ ε) →
  ∀ i j, |gsm_logits Q K tau i j - (- (2 / tau) * ‖pure_quaternion (Q i) - pure_quaternion (K j)‖^2)| ≤ C * ε^4 := by
    have h_geo_bound :
        ∃ C_geo > 0, ∀ ε > 0, ε < 1 →
          ∀ (u v : Quaternion ℝ), u.re = 0 → v.re = 0 →
            ‖u‖ ≤ ε → ‖v‖ ≤ ε →
              |(d_geo (NormedSpace.exp ℝ u) (NormedSpace.exp ℝ v)) ^ 2 - 4 * ‖u - v‖ ^ 2| ≤
                C_geo * ε ^ 4 := by
      exact small_angle_expansion;
    obtain ⟨C_geo, hC_geo_pos, hC_geo⟩ := h_geo_bound;
    refine' ⟨C_geo / 2, half_pos hC_geo_pos, fun ε hε₁ hε₂ T _ Q K tau htau hQ hK i j => _⟩;
    have h_bound :
        |(d_geo (NormedSpace.exp ℝ (pure_quaternion (Q i)))
            (NormedSpace.exp ℝ (pure_quaternion (K j)))) ^ 2 -
          4 * ‖pure_quaternion (Q i) - pure_quaternion (K j)‖ ^ 2| ≤
        C_geo * ε ^ 4 := by
      exact hC_geo ε hε₁ hε₂ _ _ (by exact rfl) (by exact rfl) (hQ i) (hK j);
    unfold gsm_logits;
    rw [abs_le] at *;
    constructor <;> ring_nf at * <;>
      nlinarith [inv_mul_cancel_left₀ (by linarith : tau ≠ 0)
        (d_geo (NormedSpace.exp ℝ (pure_quaternion (Q i)))
          (NormedSpace.exp ℝ (pure_quaternion (K j))) ^ 2),
        inv_mul_cancel_left₀ (by linarith : tau ≠ 0)
          (‖pure_quaternion (Q i) - pure_quaternion (K j)‖ ^ 2)]

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
  have h_diff :
      ∃ C > 0, ∀ ε > 0, ε < 1 → ∀ (T : ℕ) [NeZero T]
        (Q K : Fin T → Fin 3 → ℝ) (tau : ℝ),
        tau ≥ 1 →
        (∀ i, ‖pure_quaternion (Q i)‖ ≤ ε) →
        (∀ j, ‖pure_quaternion (K j)‖ ≤ ε) →
        norm_infty (fun i => norm_infty (P_gsm Q K tau i - P_std Q K tau i)) ≤
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
    refine' le_trans (norm_infty_le _ _) _;
    exact (1 / 2) * norm_infty (fun i => norm_infty (fun j => gsm_logits Q K tau i j - std_logits Q K tau i j));
    · intro i;
      refine' le_trans (le_of_eq (abs_of_nonneg (norm_infty_nonneg _))) (le_trans (h_row_stability i) _);
      refine' mul_le_mul_of_nonneg_left _ (by norm_num);
      convert norm_infty_ge_abs _ i using 1;
      rw [abs_of_nonneg (norm_infty_nonneg _)];
    · exact mul_nonneg (by norm_num) (norm_infty_nonneg _);
    · norm_num;
  obtain ⟨C, hC_pos, hC_bound⟩ := h_diff
  have h_diff_bound :
      ∃ C' > 0, ∀ ε > 0, ε < 1 → ∀ (T : ℕ) [NeZero T]
        (Q K : Fin T → Fin 3 → ℝ) (tau : ℝ),
        tau ≥ 1 →
        (∀ i, ‖pure_quaternion (Q i)‖ ≤ ε) →
        (∀ j, ‖pure_quaternion (K j)‖ ≤ ε) →
        norm_infty (fun i => norm_infty (fun j => gsm_logits Q K tau i j - std_logits Q K tau i j)) ≤ C' * ε^2 := by
    have h_diff_bound :
        ∃ C' > 0, ∀ ε > 0, ε < 1 → ∀ (T : ℕ) [NeZero T]
          (Q K : Fin T → Fin 3 → ℝ) (tau : ℝ),
          tau ≥ 1 →
          (∀ i, ‖pure_quaternion (Q i)‖ ≤ ε) →
          (∀ j, ‖pure_quaternion (K j)‖ ≤ ε) →
          ∀ i j, |gsm_logits Q K tau i j - std_logits Q K tau i j| ≤ C' * ε^2 := by
      have h_diff_bound :
          ∃ C' > 0, ∀ ε > 0, ε < 1 → ∀ (T : ℕ) [NeZero T]
            (Q K : Fin T → Fin 3 → ℝ) (tau : ℝ),
            tau ≥ 1 →
            (∀ i, ‖pure_quaternion (Q i)‖ ≤ ε) →
            (∀ j, ‖pure_quaternion (K j)‖ ≤ ε) →
            ∀ i j,
              |gsm_logits Q K tau i j -
                (- (2 / tau) * ‖pure_quaternion (Q i)‖^2 -
                  (2 / tau) * ‖pure_quaternion (K j)‖^2 +
                    4 * std_logits Q K tau i j)| ≤ C' * ε^4 := by
        obtain ⟨C', hC'_pos, hC'_bound⟩ := logits_approx;
        exact ⟨C', hC'_pos, fun ε hε₁ hε₂ T _ Q K tau htau hQ hK i j => by
          convert hC'_bound ε hε₁ hε₂ T Q K tau htau hQ hK i j using 1;
          rw [show - (2 / tau) * ‖pure_quaternion (Q i) - pure_quaternion (K j)‖ ^ 2 =
            - (2 / tau) * ‖pure_quaternion (Q i)‖ ^ 2 - 2 / tau * ‖pure_quaternion (K j)‖ ^ 2 +
              4 * std_logits Q K tau i j by
                linarith [logits_expansion Q K tau i j]]⟩;
      obtain ⟨C', hC'_pos, hC'_bound⟩ := h_diff_bound;
      refine' ⟨8 + C', by linarith, fun ε hε₁ hε₂ T _ Q K tau htau hQ hK i j => _⟩;
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
                4 * std_logits Q K tau i j) - std_logits Q K tau i j| ≤ 8 * ε ^ 2 from ?_)) ?_;
      · have h_norm_bounds :
          ‖pure_quaternion (Q i)‖^2 ≤ ε^2 ∧
            ‖pure_quaternion (K j)‖^2 ≤ ε^2 ∧
              |std_logits Q K tau i j| ≤ ε^2 := by
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
          exact abs_le.mpr ⟨
            by
              rw [std_logits_eq_inner];
              nlinarith [abs_le.mp h_inner_bound,
                mul_div_cancel₀ (1 : ℝ) (by linarith : tau ≠ 0)],
            by
              rw [std_logits_eq_inner];
              nlinarith [abs_le.mp h_inner_bound,
                mul_div_cancel₀ (1 : ℝ) (by linarith : tau ≠ 0)]⟩;
        refine' abs_le.mpr ⟨_, _⟩ <;> ring_nf at * <;>
          nlinarith [inv_pos.mpr (zero_lt_one.trans_le htau),
            mul_inv_cancel₀ (ne_of_gt (zero_lt_one.trans_le htau)),
            abs_le.mp h_norm_bounds.2.2];
      · nlinarith [show 0 ≤ C' * ε ^ 2 by positivity, show ε ^ 2 ≤ 1 by nlinarith];
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
