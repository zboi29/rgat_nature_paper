/-
Softmax and analytic bounds for attention.

This module provides the softmax definition used throughout the attention
formalization, its basic calculus properties (derivatives, sum-to-one), and
auxiliary norms used in stability/approximation bounds. The main output is the
Jacobian formula and the `1/2`-Lipschitz estimate used in Lemma S3.
-/
import Mathlib
import RgatPaperProofs.Geometry

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
### Softmax definition

For `x : Fin n → ℝ`, `softmax x i = exp(x_i) / ∑_j exp(x_j)`. This is well-defined
when `n ≠ 0` (enforced via `NeZero n` for lemmas that require positivity).
-/
noncomputable def softmax {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => Real.exp (x i) / ∑ j, Real.exp (x j)

lemma softmax_sum_one {n : ℕ} [NeZero n] (x : Fin n → ℝ) : ∑ i, softmax x i = 1 := by
  unfold softmax;
  rw [ ← Finset.sum_div, div_self <| ne_of_gt <| Finset.sum_pos ( fun _ _ => Real.exp_pos _ ) Finset.univ_nonempty ]

/-
Sum of exponentials is positive (used to justify division).
-/
lemma sum_exp_pos {n : ℕ} [NeZero n] (x : Fin n → ℝ) : 0 < ∑ j, Real.exp (x j) := by
  exact Finset.sum_pos ( fun _ _ => Real.exp_pos _ ) Finset.univ_nonempty

/-
Directional derivative of the sum of exponentials along the `j`-th basis vector.
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
Derivative of a coordinate exponential `exp(x_i)` along basis direction `j`.
-/
lemma exp_deriv_apply {n : ℕ} (x : Fin n → ℝ) (i j : Fin n) :
  fderiv ℝ (fun y => Real.exp (y i)) x (Pi.single j 1) = (if i = j then Real.exp (x i) else 0) := by
    erw [ fderiv_exp ] <;> norm_num;
    · erw [ HasFDerivAt.fderiv ( hasFDerivAt_apply _ _ ) ] ; aesop;
    · exact differentiableAt_pi.1 differentiableAt_id _

/-
### Norms

We use a sup-norm on `Fin n → ℝ` and a row-wise `∞`-of-`ℓ2` norm for matrices.
-/
noncomputable def norm_infty {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  (Finset.univ.image (fun i => |x i|)).max.getD 0

/- Euclidean (ℓ2) norm for a finite vector. -/
noncomputable def norm_l2 {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ‖x‖

/- Max-row ℓ2 norm for a matrix. -/
noncomputable def norm_infty_2 {T d : ℕ} (x : Fin T → Fin d → ℝ) : ℝ :=
  norm_infty (fun i => norm_l2 (x i))

lemma norm_l2_nonneg {n : ℕ} (x : Fin n → ℝ) : 0 ≤ norm_l2 x := by
  unfold norm_l2
  exact norm_nonneg _

/-
Jacobian entry of softmax: d/dx_j softmax_i(x) = softmax_i(x) (δ_ij - softmax_j(x)).
-/
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

/-
Basic bound: `|x_i| ≤ ‖x‖_∞`.
-/
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

lemma norm_le_norm_infty {n : ℕ} (x : Fin n → ℝ) : ‖x‖ ≤ norm_infty x := by
  have h : ∀ i, ‖x i‖ ≤ norm_infty x := by
    intro i
    simpa [Real.norm_eq_abs] using (norm_infty_ge_abs x i)
  exact (pi_norm_le_iff_of_nonneg (x := x) (r := norm_infty x) (norm_infty_nonneg x)).2 h

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
