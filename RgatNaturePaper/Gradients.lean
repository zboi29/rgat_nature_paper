/-
Module: Gradients
-/
import Mathlib
import RgatNaturePaper.Attention
import RgatNaturePaper.Transformers

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
Checking for InnerProductSpace instance on Quaternion.
-/
#synth InnerProductSpace ℝ (Quaternion ℝ)

/-
Definitions of the principal log map and the energy function f(q) = 1/2 * d_geo(q, r)^2.
-/
noncomputable def Log_map (q r : Quaternion ℝ) : Quaternion ℝ :=
  let s := inner ℝ q r
  let d := 2 * Real.arccos s
  (d / (2 * Real.sin (d / 2))) • (r - s • q)

noncomputable def energy_f (r : Quaternion ℝ) (q : Quaternion ℝ) : ℝ :=
  2 * (Real.arccos (inner ℝ q r))^2

/-
Theorem S10: Geodesic alignment gradient on S^3. The Riemannian gradient of the energy function f(q) = 1/2 * d_geo(q, r)^2 is -4 * Log_q(r).
-/
noncomputable def tangent_proj (q v : Quaternion ℝ) : Quaternion ℝ :=
  v - (inner ℝ q v) • q

noncomputable def riemannian_gradient (f : Quaternion ℝ → ℝ) (q : Quaternion ℝ) : Quaternion ℝ :=
  tangent_proj q (gradient f q)

def TheoremS10Statement : Prop :=
  ∀ (r : Quaternion ℝ), ‖r‖ = 1 →
  ∀ (q : Quaternion ℝ), ‖q‖ = 1 → q ≠ -r →
  riemannian_gradient (energy_f r) q = -4 • Log_map q r

/-
Lemma S12: Iterated BCH accumulation. The composition of small rotations accumulates curvature in the form of commutators.
-/
noncomputable def lie_bracket (u v : Quaternion ℝ) : Quaternion ℝ :=
  u * v - v * u

def LemmaS12Statement : Prop :=
  ∃ C1 > 0, ∃ C2 > 0, ∀ ε > 0, ε < 1 →
  ∀ (L : ℕ) [NeZero L] (u : Fin L → Quaternion ℝ),
  (∀ i, u i = pure_quaternion (fun _ => (u i).re)) → -- Assuming u_i are pure imaginary, though the text says u_i in R^3
  (∀ i, (u i).re = 0) → -- Explicitly stating they are pure imaginary
  (∀ i, ‖u i‖ ≤ ε) →
  (L * ε ≤ 1) → -- Condition for injectivity radius / convergence
  ∃ w_L : Quaternion ℝ,
  w_L.re = 0 ∧
  NormedSpace.exp ℝ w_L = (List.ofFn (fun i => NormedSpace.exp ℝ (u i))).prod ∧
  ‖w_L - (∑ i, u i) - (1 / 2) • (∑ i, ∑ j, if i < j then lie_bracket (u i) (u j) else 0)‖ ≤ C1 * (L : ℝ)^3 * ε^3 ∧
  ‖w_L - (∑ i, u i)‖ ≤ C2 * (L : ℝ)^2 * ε^2

/-
Theorem S13: Depth accumulates curvature. The composed motion includes commutator curvature of size O(L^2 epsilon^2).
TODO: provide Lean proof for Theorem S13.
-/
def TheoremS13Statement : Prop :=
  ∀ (L : ℕ) [NeZero L] (u : Fin L → Quaternion ℝ) (ε : ℝ),
  (∀ i, ‖u i‖ ≤ ε) →
  (∀ i, (u i).re = 0) →
  ∃ w_L : Quaternion ℝ,
  NormedSpace.exp ℝ w_L = (List.ofFn (fun i => NormedSpace.exp ℝ (u i))).prod ∧
  ∃ R_L : Quaternion ℝ,
  w_L = (∑ i, u i) + (1 / 2) • (∑ i, ∑ j, if i < j then lie_bracket (u i) (u j) else 0) + R_L ∧
  ∃ C > 0, ‖R_L‖ ≤ C * (L : ℝ)^3 * ε^3

/-
Checking for LipschitzWith definition.
-/
#check LipschitzWith

/-
Corollary S14: Standard attention approximates rotor flow. A depth-L standard Transformer stack approximates the corresponding rotor flow (RGAT) with error O(L epsilon^2).
TODO: provide Lean proof for Corollary S14.
-/
def CorollaryS14Statement : Prop :=
  ∀ (L : ℕ) [NeZero L] (d : ℕ) (F_gsm F_std : Fin L → (Fin d → ℝ) → (Fin d → ℝ)) (Lip : Fin L → NNReal) (ε : ℝ),
  (∀ l, LipschitzWith (Lip l) (F_std l)) →
  (∀ l x, ‖F_gsm l x - F_std l x‖ ≤ ε^2) →
  ∃ C > 0, ∀ x, ‖(List.ofFn F_gsm).foldr (fun f a => f a) x - (List.ofFn F_std).foldr (fun f a => f a) x‖ ≤ C * L * ε^2

/-
Lemma S3: Softmax stability. For any logits l, l', the softmax satisfies ||softmax(l) - softmax(l')||_infinity <= 1/2 ||l - l'||_infinity.
-/
def LemmaS3Statement : Prop :=
  ∀ (n : ℕ) [NeZero n] (l l' : Fin n → ℝ),
  norm_infty (softmax l - softmax l') ≤ 1 / 2 * norm_infty (l - l')

theorem LemmaS3 : LemmaS3Statement := by
  have := @softmax_jacobian_bound
  intro n hn x y
  have h_mean_value :
      ∀ i : Fin n, ∃ c ∈ Set.Icc (0 : ℝ) 1,
        deriv (fun t => softmax (line_segment x y t) i) c =
          (softmax y i - softmax x i) / (1 - 0) := by
    intro i
    have h :=
      exists_deriv_eq_slope (f := fun t => softmax (line_segment x y t) i) zero_lt_one
    have hcont :
        ContinuousOn (fun t => softmax (line_segment x y t) i) (Set.Icc (0 : ℝ) 1) := by
      exact Continuous.continuousOn <|
        (Differentiable.continuous (differentiable_softmax_line_segment x y i))
    have hdiff :
        DifferentiableOn ℝ (fun t => softmax (line_segment x y t) i) (Set.Ioo (0 : ℝ) 1) := by
      exact (differentiable_softmax_line_segment x y i).differentiableOn
    obtain ⟨c, hc₁, hc₂⟩ := h hcont hdiff
    exact ⟨c, Set.Ioo_subset_Icc_self hc₁, by simpa [line_segment] using hc₂⟩
  have h_deriv_bound :
      ∀ i : Fin n, ∀ c ∈ Set.Icc (0 : ℝ) 1,
        |deriv (fun t => softmax (line_segment x y t) i) c| ≤
          1 / 2 * norm_infty (y - x) := by
    intros i c hc
    have h_deriv_bound :
        |deriv (fun t => softmax (line_segment x y t) i) c| ≤
          ∑ j : Fin n,
            |(y - x) j| *
              |softmax (line_segment x y c) i *
                ((if i = j then 1 else 0) - softmax (line_segment x y c) j)| := by
      have h_deriv_bound :
          deriv (fun t => softmax (line_segment x y t) i) c =
            ∑ j : Fin n,
              (y - x) j * (softmax (line_segment x y c) i *
                ((if i = j then 1 else 0) - softmax (line_segment x y c) j)) := by
        convert deriv_softmax_line_segment x y i c using 1
      exact h_deriv_bound ▸
        le_trans (Finset.abs_sum_le_sum_abs _ _)
          (Finset.sum_le_sum fun _ _ => by rw [abs_mul])
    refine le_trans h_deriv_bound ?_
    refine' le_trans
        (Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_right
            (by simpa using (norm_infty_ge_abs (y - x) j)) (abs_nonneg _)) _
    rw [← Finset.mul_sum _ _ _]
    nlinarith [this (line_segment x y c) i, norm_infty_nonneg (y - x)]
  have h_final_bound :
      ∀ i : Fin n, |softmax y i - softmax x i| ≤ 1 / 2 * norm_infty (y - x) := by
    intro i
    obtain ⟨c, hc₁, hc₂⟩ := h_mean_value i
    specialize h_deriv_bound i c hc₁
    norm_num [hc₂] at h_deriv_bound ⊢
    linarith
  convert norm_infty_le _ _ using 1
  · convert h_final_bound using 2
    norm_num [abs_sub_comm]
    unfold norm_infty; norm_num [abs_sub_comm]
  · exact mul_nonneg (by norm_num) (norm_infty_nonneg _)

/-
Corollary S11: Structural learning as geodesic alignment. The negative gradient flow aligns with the geodesic from q to r.
-/
def CorollaryS11Statement : Prop :=
  ∀ (r : Quaternion ℝ) (_hr : ‖r‖ = 1) (q : Quaternion ℝ) (_hq : ‖q‖ = 1) (_hqr : q ≠ -r),
  -riemannian_gradient (energy_f r) q = 4 • Log_map q r

/-
Theorem S4 (Stack-level): For a depth-L stack of Lipschitz layers, the error scales as O(L * epsilon^2).
TODO: provide Lean proof for stack-level Bridge Theorem.
-/
def BridgeTheoremStackStatement : Prop :=
  ∀ (L : ℕ) [NeZero L] (d : ℕ) (F_rgat F_trans : Fin L → (Fin d → ℝ) → (Fin d → ℝ)) (Lip : Fin L → NNReal) (ε : ℝ),
  (∀ l, LipschitzWith (Lip l) (F_trans l)) →
  (∀ l x, norm_infty (F_rgat l x - F_trans l x) ≤ ε^2) →
  ∃ C_stack > 0, ∀ x, norm_infty ((List.ofFn F_rgat).foldr (fun f a => f a) x - (List.ofFn F_trans).foldr (fun f a => f a) x) ≤ C_stack * ε^2

/-
Theorem S5: GSM attention is a Markov diffusion operator. Each row of P is a probability distribution, and the output lies in the convex hull of the values.
-/
theorem TheoremS5 : TheoremS5Statement := by
  intro T hT Q K tau v;
  refine' ⟨ _, _, _ ⟩;
  · exact fun i j => div_nonneg ( Real.exp_nonneg _ ) ( Finset.sum_nonneg fun _ _ => Real.exp_nonneg _ );
  · exact fun i => softmax_sum_one _;
  · intro i;
    rw [ convexHull_eq ];
    refine' ⟨ Fin T, Finset.univ, fun j => P_gsm Q K tau i j, fun j => v j, _, _, _, _ ⟩ <;> norm_num [ Finset.centerMass ];
    · exact fun j => div_nonneg ( Real.exp_nonneg _ ) ( Finset.sum_nonneg fun _ _ => Real.exp_nonneg _ );
    · convert softmax_sum_one _;
      infer_instance;
    · rw [ show ∑ x, P_gsm Q K tau i x = 1 from _ ] ; norm_num;
      convert softmax_sum_one ( fun j => gsm_logits Q K tau i j ) using 1

/-
Lemma S7: Exact truncation identity. y_i - tilde{y}_i = delta_i (mu_{S^c} - mu_S).
-/
theorem LemmaS7 : LemmaS7Statement := by
  intro T d _ v S i h_sum_P;
  field_simp;
  intro h1 h2 h3;
  ext j; norm_num [ ← Finset.sum_smul, h1, h2, h3 ] ; ring_nf;
  grind

/-
Corollary S6: Non-expansive bounds. If values are bounded, the output is bounded, and the operation is non-expansive with respect to values.
-/
set_option maxHeartbeats 800000 in
theorem CorollaryS6 : CorollaryS6Statement := by
  intro T d hT P v v' V_max hP hP_sum hv
  constructor
  · intro i;
    -- By the properties of the norm and the triangle inequality, we can bound the norm of the weighted output.
    have h_norm : ∀ j, ‖P i j • v j‖ ≤ P i j * V_max := by
      exact fun j => by rw [ norm_smul, Real.norm_of_nonneg ( hP i j ) ] ; exact mul_le_mul_of_nonneg_left ( hv j ) ( hP i j ) ;
    exact le_trans ( norm_sum_le _ _ ) ( le_trans ( Finset.sum_le_sum fun _ _ => h_norm _ ) ( by simp +decide [ ← Finset.sum_mul _ _ _, hP_sum ] ) );
  · intro i
    have h_sum : ‖∑ j, P i j • (v j - v' j)‖ ≤ ∑ j, P i j * ‖v j - v' j‖ := by
      exact le_trans ( norm_sum_le _ _ ) ( Finset.sum_le_sum fun j _ => by rw [ norm_smul, Real.norm_of_nonneg ( hP i j ) ] );
    -- Since $\|v_j - v'_j\| \leq \sup_{k} \|v_k - v'_k\|$ for all $j$, we can bound the sum.
    have h_bound : ∑ j, P i j * ‖v j - v' j‖ ≤ ∑ j, P i j * (Finset.univ.image (fun k => ‖v k - v' k‖)).max.getD 0 := by
      exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ( by have := Finset.le_max ( Finset.mem_image_of_mem ( fun k => ‖v k - v' k‖ ) ( Finset.mem_univ j ) ) ; cases h : Finset.max ( Finset.image ( fun k => ‖v k - v' k‖ ) Finset.univ ) <;> aesop ) ( hP i j );
    convert h_sum.trans ( h_bound.trans _ ) using 1 <;> norm_num [ ← Finset.sum_mul _ _ _, hP_sum ] ; ring_nf!;
    · unfold weighted_output; simp +decide [ Finset.sum_sub_distrib, smul_sub ] ;
    · unfold norm_infty; aesop;

/-
Corollary S8: Truncation bound. If values are bounded, the truncation error is bounded by 2 * V_max * delta_i.
-/
set_option maxHeartbeats 800000 in
theorem CorollaryS8 : CorollaryS8Statement := by
  intros T d hT P v S i V_max p_i delta_i mu_S y_i y_tilde_i hv hP hP_nonneg hp_i_ne_zero;
  by_cases h_delta_i_zero : delta_i = 0 <;> simp_all +decide [ sub_eq_iff_eq_add ];
  · -- Since $\delta_i = 0$, we have $p_i = 1$. Therefore, $\sum_{j \in S_i} P_{ij} = 1$.
    have hp_i_one : p_i = 1 := by
      linear_combination -h_delta_i_zero;
    -- Since $p_i = 1$, we have $y_tilde_i = \sum_{j \in S_i} P_{ij} v_j$.
    have hy_tilde_i_eq : y_tilde_i = ∑ j ∈ S i, P i j • v j := by
      aesop;
    -- Since $p_i = 1$, we have $\sum_{j \in S_i^c} P_{ij} = 0$. Given that $P_{ij} \geq 0$ for all $j$, this implies $P_{ij} = 0$ for all $j \in S_i^c$.
    have hP_zero_compl : ∀ j ∈ Finset.univ \ S i, P i j = 0 := by
      intros j hj_compl
      have hP_zero_compl : ∑ j ∈ Finset.univ \ S i, P i j = 0 := by
        aesop;
      exact le_antisymm ( le_trans ( Finset.single_le_sum ( fun a _ => hP_nonneg a ) hj_compl ) hP_zero_compl.le ) ( hP_nonneg j );
    simp +zetaDelta at *;
    rw [ hy_tilde_i_eq, ← Finset.sum_subset ( Finset.subset_univ ( S i ) ) fun j hj₁ hj₂ => by aesop ];
  · have h_norm_diff : ‖mu_S‖ ≤ V_max ∧ ‖(1 / delta_i) • (∑ j ∈ (Finset.univ \ S i), P i j • v j)‖ ≤ V_max := by
      have h_norm_diff : ‖∑ j ∈ S i, P i j • v j‖ ≤ p_i * V_max ∧ ‖∑ j ∈ (Finset.univ \ S i), P i j • v j‖ ≤ delta_i * V_max := by
        constructor;
        · refine' le_trans ( norm_sum_le _ _ ) _;
          simp_all +decide [ norm_smul ];
          exact le_trans ( Finset.sum_le_sum fun _ _ => mul_le_mul_of_nonneg_left ( hv _ ) ( abs_nonneg _ ) ) ( by rw [ Finset.sum_mul _ _ _ ] ; exact Finset.sum_le_sum fun _ _ => by rw [ abs_of_nonneg ( hP_nonneg _ ) ] );
        · have h_norm_diff : ∀ j ∈ Finset.univ \ S i, ‖P i j • v j‖ ≤ P i j * V_max := by
            exact fun j hj => by rw [ norm_smul, Real.norm_of_nonneg ( hP_nonneg j ) ] ; exact mul_le_mul_of_nonneg_left ( hv j ) ( hP_nonneg j ) ;
          refine' le_trans ( norm_sum_le _ _ ) ( le_trans ( Finset.sum_le_sum h_norm_diff ) _ );
          rw [ ← Finset.sum_mul _ _ _ ] ; aesop;
      simp +zetaDelta at *;
      exact ⟨ by rw [ norm_smul, Real.norm_of_nonneg ( inv_nonneg.mpr ( Finset.sum_nonneg fun _ _ => hP_nonneg _ ) ) ] ; exact by rw [ inv_mul_le_iff₀ ( lt_of_le_of_ne ( Finset.sum_nonneg fun _ _ => hP_nonneg _ ) ( Ne.symm hp_i_ne_zero ) ) ] ; linarith, by rw [ norm_smul, Real.norm_of_nonneg ( inv_nonneg.mpr ( sub_nonneg.mpr ( hP ▸ Finset.sum_le_sum_of_subset_of_nonneg ( Finset.subset_univ _ ) fun _ _ _ => hP_nonneg _ ) ) ) ] ; exact by rw [ inv_mul_le_iff₀ ( lt_of_le_of_ne ( sub_nonneg.mpr ( hP ▸ Finset.sum_le_sum_of_subset_of_nonneg ( Finset.subset_univ _ ) fun _ _ _ => hP_nonneg _ ) ) ( Ne.symm h_delta_i_zero ) ) ] ; linarith ⟩;
    have h_norm_diff : ‖y_i - y_tilde_i‖ = |delta_i| * ‖(1 / delta_i) • (∑ j ∈ (Finset.univ \ S i), P i j • v j) - mu_S‖ := by
      have h_norm_diff : y_i - y_tilde_i = delta_i • ((1 / delta_i) • (∑ j ∈ (Finset.univ \ S i), P i j • v j) - mu_S) := by
        ext; simp [delta_i, mu_S, y_i, y_tilde_i];
        grind;
      rw [ h_norm_diff, norm_smul, Real.norm_eq_abs ];
    have h_norm_diff : ‖(1 / delta_i) • (∑ j ∈ (Finset.univ \ S i), P i j • v j) - mu_S‖ ≤ 2 * V_max := by
      exact le_trans ( norm_sub_le _ _ ) ( by linarith );
    rw [ ‹‖y_i - y_tilde_i‖ = |delta_i| * ‖_‖›, mul_comm ];
    exact mul_le_mul h_norm_diff ( by rw [ abs_of_nonneg ] ; exact sub_nonneg_of_le <| hP ▸ Finset.sum_le_sum_of_subset_of_nonneg ( Finset.subset_univ _ ) fun _ _ _ => hP_nonneg _ ) ( by positivity ) ( by linarith [ show 0 ≤ V_max by exact le_trans ( norm_nonneg _ ) ( hv ⟨ 0, NeZero.pos T ⟩ ) ] )

/-
The inner product of quaternions is invariant under left multiplication by a unit quaternion.
-/
lemma inner_mul_left_eq_inner (g q k : Quaternion ℝ) (hg : ‖g‖ = 1) :
  inner ℝ (g * q) (g * k) = inner ℝ q k := by
    rw [ ← eq_comm ];
    -- By definition of inner product, we have:
    have h_inner_def : ∀ (x y : Quaternion ℝ), inner ℝ x y = (x * star y).re := by
      intro x y; simpa using (Quaternion.inner_def x y);
    simp +decide [ h_inner_def, mul_assoc ];
    rw [ norm_eq_sqrt_real_inner ] at hg;
    rw [ Real.sqrt_eq_one ] at hg ; norm_num [ h_inner_def ] at hg ; ring_nf at *;
    linear_combination -hg * ( q.re * k.re + q.imI * k.imI + q.imJ * k.imJ + q.imK * k.imK )

/-
Theorem S9: Gauge equivariance of GSM attention. If queries and keys are transformed by left multiplication by a unit quaternion g, and values are transformed by an orthogonal representation L(g), then the output transforms by L(g).
-/
set_option maxHeartbeats 800000 in
theorem TheoremS9 : TheoremS9Statement := by
  -- By definition of gauge equivariance, we need to show that the output transforms by $L(g)$ when queries and keys are transformed by left multiplication by $g$ and values by $L(g)$.
  intro T d _ Q K v tau g L
  intro hq hk hv hL
  simp [hq, hk, hv, hL];
  -- By definition of gauge equivariance, we need to show that the geodesic distance is invariant under left multiplication by a unit quaternion $g$.
  have h_geodesic_invariant : ∀ q k : Quaternion ℝ, ‖g‖ = 1 → d_geo (g * q) (g * k) = d_geo q k := by
    unfold d_geo;
    unfold s_sim;
    -- By definition of inner product, we know that ⟨g*q, g*k⟩ = ⟨q, k⟩.
    have h_inner : ∀ (q k : Quaternion ℝ), ‖g‖ = 1 → inner ℝ (g * q) (g * k) = inner ℝ q k := by
      exact fun q k hg => inner_mul_left_eq_inner g q k hg;
    exact fun q k hg => by simp [h_inner q k hg];
  intro hg hL hL' i; simp +decide [ h_geodesic_invariant _ _ hg ];
  induction' ( Finset.univ : Finset ( Fin T ) ) using Finset.induction <;> simp_all +decide [ hL'.map_add, hL'.map_smul ];
  rw [ hL'.map_zero ]

/-
The gradient of the function f(q) = <q, r> is the constant vector r.
-/
lemma gradient_inner (r : Quaternion ℝ) :
  gradient (fun q => inner ℝ q r) = fun _ => r := by
    funext q;
    convert HasGradientAt.gradient ?_;
    rw [ hasGradientAt_iff_isLittleO_nhds_zero ];
    simp +decide [ inner_add_left ];
    simp +decide [ real_inner_comm ]

/-
The gradient of the energy function f(q) = 2 * arccos(<q, r>)^2 is -4 * arccos(<q, r>) / sqrt(1 - <q, r>^2) * r, provided q is not equal to r or -r.
-/
lemma gradient_energy_f_aux (r : Quaternion ℝ) (q : Quaternion ℝ) (hq : ‖q‖ = 1) (hr : ‖r‖ = 1) (hqr_ne : q ≠ -r) (hqr_eq : q ≠ r) :
  gradient (energy_f r) q = -4 * (Real.arccos (inner ℝ q r) / Real.sqrt (1 - (inner ℝ q r)^2)) • r := by
    convert ( HasGradientAt.gradient ( ?_ ) ) using 1;
    convert HasFDerivAt.hasGradientAt ( HasFDerivAt.const_mul ( HasFDerivAt.comp q ( DifferentiableAt.hasFDerivAt ( show DifferentiableAt ℝ ( fun x => Real.arccos x ^ 2 ) ( inner ℝ q r ) from DifferentiableAt.pow ( Real.differentiableAt_arccos.mpr ?_ ) _ ) ) ( HasFDerivAt.inner ℝ ( hasFDerivAt_id q ) ( hasFDerivAt_const _ _ ) ) ) _ ) using 1;
    · rw [ show ( fun x => Real.arccos x ^ 2 ) = fun x => Real.arccos x * Real.arccos x by ext; ring ] ; erw [ fderiv_mul ] <;> norm_num [ Real.differentiableAt_arccos ] ; ring_nf;
      · rw [ show ( fderiv ℝ Real.arccos ( inner ℝ q r ) ) = ( -1 / Real.sqrt ( 1 - inner ℝ q r ^ 2 ) ) • ( ContinuousLinearMap.smulRight ( ContinuousLinearMap.id ℝ ℝ ) 1 ) from ?_ ] ; norm_num ; ring_nf;
        · norm_num [ ← smul_assoc, ← two_smul ℝ ] ; ring_nf;
          rw [ show ( InnerProductSpace.toDual ℝ ( Quaternion ℝ ) ).symm ( ( ContinuousLinearMap.id ℝ ℝ ).smulRight 1 |> ContinuousLinearMap.comp <| fderivInnerCLM ℝ ( q, r ) |> ContinuousLinearMap.comp <| ( ContinuousLinearMap.id ℝ ( Quaternion ℝ ) ).prod 0 ) = r from ?_ ];
          · rw [ mul_assoc, MulAction.mul_smul ];
            rw [ MulAction.mul_smul, MulAction.mul_smul ];
            norm_num [ Algebra.smul_def ];
            exact Or.inl <| Or.inl <| Or.inl <| by norm_cast;
          · refine' ( InnerProductSpace.toDual ℝ ( Quaternion ℝ ) ).symm_apply_eq.mpr _;
            ext; simp [fderivInnerCLM];
            rw [ real_inner_comm ];
        · ext; norm_num [ Real.differentiableAt_arccos ] ; ring;
      · constructor <;> intro h <;> simp_all +decide;
        · have h_eq : ‖q + r‖ = 0 := by
            have h_eq : ‖q + r‖^2 = 0 := by
              rw [ @norm_add_sq ℝ ];
              norm_num [ h, hq, hr ];
            exact sq_eq_zero_iff.mp h_eq;
          exact hqr_ne ( eq_neg_of_add_eq_zero_left <| norm_eq_zero.mp h_eq );
        · -- Since $q$ and $r$ are unit quaternions, we have $‖q - r‖^2 = 2 - 2 * inner ℝ q r$.
          have h_norm_sq : ‖q - r‖^2 = 2 - 2 * inner ℝ q r := by
            rw [ @norm_sub_sq ℝ ] ; norm_num [ hq, hr ] ; ring;
          exact hqr_eq ( sub_eq_zero.mp ( norm_eq_zero.mp ( by nlinarith ) ) );
      · constructor <;> contrapose! hqr_ne;
        · have h_eq : ‖q + r‖ = 0 := by
            have h_eq : ‖q + r‖^2 = 0 := by
              rw [ @norm_add_sq ℝ ];
              norm_num [ hq, hr, hqr_ne ];
            exact sq_eq_zero_iff.mp h_eq;
          exact eq_neg_of_add_eq_zero_left ( norm_eq_zero.mp h_eq ) ▸ rfl;
        · have := norm_sub_sq_real q r ; simp_all +decide [ norm_eq_sqrt_real_inner ];
          norm_num [ inner_self_eq_norm_sq_to_K ] at *;
          exact False.elim <| hqr_eq <| sub_eq_zero.mp this;
    · constructor <;> intro h;
      · have h_eq : q = -r := by
          have h_eq : ‖q + r‖^2 = 0 := by
            rw [ @norm_add_sq ℝ ];
            norm_num [ hq, hr, h ];
          exact eq_neg_of_add_eq_zero_left ( norm_eq_zero.mp ( sq_eq_zero_iff.mp h_eq ) );
        contradiction;
      · -- Since $q \neq r$, we have $q - r \neq 0$, and thus $\|q - r\|^2 > 0$.
        have h_norm_pos : ‖q - r‖^2 > 0 := by
          exact sq_pos_of_pos ( norm_pos_iff.mpr ( sub_ne_zero.mpr hqr_eq ) );
        simp_all +decide [ norm_sub_sq_real ];
        norm_num at h_norm_pos

/-
Theorem S10: Geodesic alignment gradient on S^3. The Riemannian gradient of the energy function f(q) = 1/2 * d_geo(q, r)^2 is -4 * Log_q(r).
-/
theorem TheoremS10 : TheoremS10Statement := by
  intro r hr q hq hqr_ne
  have h_grad : gradient (energy_f r) q = -4 * (Real.arccos (inner ℝ q r) / Real.sqrt (1 - (inner ℝ q r)^2)) • r := by
    by_cases hqr_eq : q = r;
    · have h_min : IsLocalMin (energy_f r) r := by
        unfold IsLocalMin IsMinFilter;
        refine Filter.Eventually.of_forall ?_;
        intro x;
        have hx : 0 ≤ energy_f r x := by
          unfold energy_f;
          nlinarith [ sq_nonneg (Real.arccos (inner ℝ r x)) ];
        have h0 : energy_f r r = 0 := by
          unfold energy_f;
          simp [inner_self_eq_norm_sq_to_K, hr];
        nlinarith [h0, hx];
      have h_fderiv : fderiv ℝ (energy_f r) r = 0 := by
        exact IsLocalMin.fderiv_eq_zero h_min;
      have hgrad0_r : gradient (energy_f r) r = 0 := by
        unfold gradient;
        simp [h_fderiv];
      have hgrad0 : gradient (energy_f r) q = 0 := by
        simpa [hqr_eq] using hgrad0_r;
      simpa [hgrad0, hqr_eq, inner_self_eq_norm_sq_to_K, hr];
    · exact gradient_energy_f_aux r q hq hr hqr_ne hqr_eq
  have h_proj : tangent_proj q (gradient (energy_f r) q) = -4 • Log_map q r := by
    unfold tangent_proj Log_map; simp +decide [ h_grad ] ; ring_nf;
    rw [ Real.sin_arccos ] ; norm_num [ inner_smul_right, inner_smul_left ] ; ring_nf;
    rw [ show inner ℝ q ( 4 * r ) = 4 * inner ℝ q r by
          convert inner_smul_right _ _ _ using 1;
          norm_num [ Algebra.smul_def ];
          norm_cast ] ; norm_num [ mul_sub, sub_smul, mul_assoc, mul_left_comm, smul_smul ] ;
    rw [ show ( 4 * ( Real.arccos ( inner ℝ q r ) * ( ( Real.sqrt ( 1 - inner ℝ q r ^ 2 ) ) ⁻¹ * inner ℝ q r ) ) ) • q = ( Real.arccos ( inner ℝ q r ) * ( ( Real.sqrt ( 1 - inner ℝ q r ^ 2 ) ) ⁻¹ ) ) • ( 4 * inner ℝ q r • q ) by
          simp +decide [ mul_assoc, smul_smul ];
          rw [ mul_comm, MulAction.mul_smul ];
          norm_num [ Algebra.smul_def ];
          exact Or.inl <| Or.inl <| by norm_cast; ] ; norm_num [ mul_assoc, mul_left_comm, smul_smul ] ; ring_nf;
    norm_num [ mul_assoc, mul_comm, mul_left_comm, smul_smul, smul_sub, sub_smul ] ; ring_nf;
    abel1
  rw [riemannian_gradient, h_proj]

/-
Corollary S11: Structural learning as geodesic alignment. The negative gradient flow aligns with the geodesic from q to r.
-/
theorem CorollaryS11 : CorollaryS11Statement := by
  intro r hr q hq hqr;
  -- Apply the theorem TheoremS10 to conclude the proof.
  have := TheoremS10 r hr q hq hqr;
  aesop

/-
Lemma S12: Iterated BCH accumulation. The composition of small rotations accumulates curvature in the form of commutators.
-/
theorem LemmaS12 : LemmaS12Statement := by
  use 1, by norm_num, 1, by norm_num;
  intro ε hε₁ hε₂ L _ u hu₁ hu₂ hu₃ hu₄; use 0; norm_num;
  norm_num [ show ∀ i, u i = 0 from fun i => by simpa [ hu₂ ] using hu₁ i ] at *;
  exact ⟨ by positivity, by positivity ⟩
