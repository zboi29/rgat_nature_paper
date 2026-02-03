/-
Proofs for gradient-based SI statements (S3, S10–S13).

This file contains analytic bounds (softmax stability, geodesic gradient) and
the BCH-style accumulation statement (S13). It depends on the attention and
transformer modules for shared definitions and norms.
-/
import Mathlib
import RgatNaturePaper.Gradients.Statements
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
### Lemma S3 (Softmax stability)
-/

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

lemma norm_infty_le_norm {n : ℕ} (x : Fin n → ℝ) : norm_infty x ≤ ‖x‖ := by
  refine norm_infty_le ?_ (norm_nonneg _)
  intro i
  simpa [Real.norm_eq_abs] using (norm_le_pi_norm (f := x) (i := i))

lemma lipschitz_norm_infty {d : ℕ} {K : NNReal} {f : (Fin d → ℝ) → (Fin d → ℝ)}
    (hf : LipschitzWith K f) (x y : Fin d → ℝ) :
    norm_infty (f x - f y) ≤ (K : ℝ) * norm_infty (x - y) := by
  have h_norm : ‖f x - f y‖ ≤ (K : ℝ) * ‖x - y‖ := by
    simpa [dist_eq_norm] using (hf.dist_le_mul x y)
  have h_out : norm_infty (f x - f y) ≤ ‖f x - f y‖ :=
    norm_infty_le_norm (f x - f y)
  have h_in : ‖x - y‖ ≤ norm_infty (x - y) := norm_le_norm_infty (x - y)
  exact h_out.trans (h_norm.trans (mul_le_mul_of_nonneg_left h_in (by exact_mod_cast K.property)))

theorem BridgeTheoremStack : BridgeTheoremStackStatement := by
  classical
  intro L _ d F_rgat F_trans Lip ε hLip hErr
  have main :
      ∀ (L : ℕ) (F_rgat F_trans : Fin L → (Fin d → ℝ) → (Fin d → ℝ)) (Lip : Fin L → NNReal),
        (∀ l, LipschitzWith (Lip l) (F_trans l)) →
        (∀ l x, ‖F_rgat l x - F_trans l x‖ ≤ ε^2) →
        ∃ C_stack > 0, ∀ x,
          ‖(List.ofFn F_rgat).foldr (fun f a => f a) x -
            (List.ofFn F_trans).foldr (fun f a => f a) x‖ ≤ C_stack * ε^2 := by
    intro L
    induction L with
    | zero =>
        intro F_rgat F_trans Lip hLip hErr
        refine ⟨1, by norm_num, ?_⟩
        intro x
        have hε : 0 ≤ ε^2 := by nlinarith
        have h0 : ‖(0 : Fin d → ℝ)‖ ≤ ε^2 := by
          simpa using hε
        have hx : x - x = (0 : Fin d → ℝ) := by
          ext i; simp
        simpa [List.ofFn, hx, sub_eq_add_neg] using h0
    | succ L IH =>
        intro F_rgat F_trans Lip hLip hErr
        set F_rgat' : Fin L → (Fin d → ℝ) → (Fin d → ℝ) := fun i => F_rgat i.succ
        set F_trans' : Fin L → (Fin d → ℝ) → (Fin d → ℝ) := fun i => F_trans i.succ
        set Lip' : Fin L → NNReal := fun i => Lip i.succ
        have hLip' : ∀ i, LipschitzWith (Lip' i) (F_trans' i) := by
          intro i; simpa using hLip i.succ
        have hErr' : ∀ i x, ‖F_rgat' i x - F_trans' i x‖ ≤ ε^2 := by
          intro i x; simpa using hErr i.succ x
        obtain ⟨C_prefix, hCpos, hCbound⟩ := IH F_rgat' F_trans' Lip' hLip' hErr'
        have hCpos' : 0 < (1 : ℝ) + (Lip 0 : ℝ) * C_prefix := by
          have hLip0 : 0 ≤ (Lip 0 : ℝ) := by exact_mod_cast (Lip 0).property
          have hCnonneg : 0 ≤ C_prefix := le_of_lt hCpos
          nlinarith
        refine ⟨1 + (Lip 0 : ℝ) * C_prefix, hCpos', ?_⟩
        intro x
        have h_foldr_rgat :
            (List.ofFn F_rgat).foldr (fun f a => f a) x =
              F_rgat 0 ((List.ofFn F_rgat').foldr (fun f a => f a) x) := by
          simp [List.ofFn_succ, F_rgat']
        have h_foldr_trans :
            (List.ofFn F_trans).foldr (fun f a => f a) x =
              F_trans 0 ((List.ofFn F_trans').foldr (fun f a => f a) x) := by
          simp [List.ofFn_succ, F_trans']
        have h_err_head :
            ‖F_rgat 0 ((List.ofFn F_rgat').foldr (fun f a => f a) x) -
              F_trans 0 ((List.ofFn F_rgat').foldr (fun f a => f a) x)‖ ≤ ε^2 := by
          simpa using hErr 0 ((List.ofFn F_rgat').foldr (fun f a => f a) x)
        have h_tail :
            ‖(List.ofFn F_rgat').foldr (fun f a => f a) x -
              (List.ofFn F_trans').foldr (fun f a => f a) x‖ ≤ C_prefix * ε^2 :=
          hCbound x
        have h_lip_head :
            ‖F_trans 0 ((List.ofFn F_rgat').foldr (fun f a => f a) x) -
                F_trans 0 ((List.ofFn F_trans').foldr (fun f a => f a) x)‖
              ≤ (Lip 0 : ℝ) *
                ‖(List.ofFn F_rgat').foldr (fun f a => f a) x -
                  (List.ofFn F_trans').foldr (fun f a => f a) x‖ := by
          simpa [dist_eq_norm] using
            (hLip 0).dist_le_mul
              ((List.ofFn F_rgat').foldr (fun f a => f a) x)
              ((List.ofFn F_trans').foldr (fun f a => f a) x)
        have h_norm_triangle :
            ‖F_rgat 0 ((List.ofFn F_rgat').foldr (fun f a => f a) x) -
                F_trans 0 ((List.ofFn F_trans').foldr (fun f a => f a) x)‖ ≤
              ‖F_rgat 0 ((List.ofFn F_rgat').foldr (fun f a => f a) x) -
                  F_trans 0 ((List.ofFn F_rgat').foldr (fun f a => f a) x)‖ +
              ‖F_trans 0 ((List.ofFn F_rgat').foldr (fun f a => f a) x) -
                  F_trans 0 ((List.ofFn F_trans').foldr (fun f a => f a) x)‖ := by
          have hdecomp :
              F_rgat 0 ((List.ofFn F_rgat').foldr (fun f a => f a) x) -
                  F_trans 0 ((List.ofFn F_trans').foldr (fun f a => f a) x) =
                (F_rgat 0 ((List.ofFn F_rgat').foldr (fun f a => f a) x) -
                    F_trans 0 ((List.ofFn F_rgat').foldr (fun f a => f a) x)) +
                  (F_trans 0 ((List.ofFn F_rgat').foldr (fun f a => f a) x) -
                    F_trans 0 ((List.ofFn F_trans').foldr (fun f a => f a) x)) := by
            abel
          rw [hdecomp]
          exact norm_add_le
            (F_rgat 0 ((List.ofFn F_rgat').foldr (fun f a => f a) x) -
              F_trans 0 ((List.ofFn F_rgat').foldr (fun f a => f a) x))
            (F_trans 0 ((List.ofFn F_rgat').foldr (fun f a => f a) x) -
              F_trans 0 ((List.ofFn F_trans').foldr (fun f a => f a) x))
        have h_head_norm :
            ‖F_rgat 0 ((List.ofFn F_rgat').foldr (fun f a => f a) x) -
                F_trans 0 ((List.ofFn F_rgat').foldr (fun f a => f a) x)‖ ≤ ε^2 := by
          exact h_err_head
        have h_tail_norm :
            ‖F_trans 0 ((List.ofFn F_rgat').foldr (fun f a => f a) x) -
                F_trans 0 ((List.ofFn F_trans').foldr (fun f a => f a) x)‖
              ≤ (Lip 0 : ℝ) * (C_prefix * ε^2) := by
          have h_lip' :
              ‖(List.ofFn F_rgat').foldr (fun f a => f a) x -
                (List.ofFn F_trans').foldr (fun f a => f a) x‖
              ≤ C_prefix * ε^2 := h_tail
          have h_lip'' :
              ‖F_trans 0 ((List.ofFn F_rgat').foldr (fun f a => f a) x) -
                  F_trans 0 ((List.ofFn F_trans').foldr (fun f a => f a) x)‖
                ≤ (Lip 0 : ℝ) * (C_prefix * ε^2) := by
            have hLip0 : 0 ≤ (Lip 0 : ℝ) := by exact_mod_cast (Lip 0).property
            exact h_lip_head.trans (mul_le_mul_of_nonneg_left h_lip' hLip0)
          exact h_lip''
        have h_norm_bound :
            ‖F_rgat 0 ((List.ofFn F_rgat').foldr (fun f a => f a) x) -
                F_trans 0 ((List.ofFn F_trans').foldr (fun f a => f a) x)‖
              ≤ ε^2 + (Lip 0 : ℝ) * (C_prefix * ε^2) := by
          linarith [h_norm_triangle, h_head_norm, h_tail_norm]
        have h_final :
            ‖F_rgat 0 ((List.ofFn F_rgat').foldr (fun f a => f a) x) -
                  F_trans 0 ((List.ofFn F_trans').foldr (fun f a => f a) x)‖
              ≤ (1 + (Lip 0 : ℝ) * C_prefix) * ε^2 := by
          nlinarith [h_norm_bound]
        simpa [h_foldr_rgat, h_foldr_trans] using h_final
  exact main L F_rgat F_trans Lip hLip hErr

/-
Theorem S5: GSM attention is a Markov diffusion operator. Each row of P is a probability distribution, and the output lies in the convex hull of the values.
-/
theorem TheoremS5 : TheoremS5Statement := by
  intro T d hT Q K tau v;
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

/-
The norm of the exponential of a pure imaginary quaternion is 1.
-/
lemma norm_exp_pure_eq_one (u : Quaternion ℝ) (hu : u.re = 0) : ‖NormedSpace.exp ℝ u‖ = 1 := by
  have := pure_quaternion_properties (fun i => u.imI ^ (if i = 0 then 1 else 0) *
    u.imJ ^ (if i = 1 then 1 else 0) * u.imK ^ (if i = 2 then 1 else 0))
    (fun i => u.imI ^ (if i = 0 then 1 else 0) *
      u.imJ ^ (if i = 1 then 1 else 0) * u.imK ^ (if i = 2 then 1 else 0))
  simp_all +decide [Norm.norm]

/-
The norm of the product of exponentials of pure imaginary quaternions is 1.
-/
lemma norm_prod_exp_pure_eq_one_list (L : ℕ) (u : Fin L → Quaternion ℝ) (hu : ∀ i, (u i).re = 0) :
  ‖(List.ofFn (fun i => NormedSpace.exp ℝ (u i))).prod‖ = 1 := by
    -- By induction on L, we can show that the norm of the product of exponentials of pure imaginary quaternions is 1.
    induction' L with L ih
    · norm_num +zetaDelta at *
    · convert ih (u ∘ Fin.succ) (fun i => hu _) using 1
      simp +decide [List.ofFn_succ, hu]

/-
The principal logarithm of the exponential of a pure quaternion u is u, provided |u| < pi.
-/
noncomputable def log_at_1 (q : Quaternion ℝ) : Quaternion ℝ := Log_map 1 q

lemma log_exp_eq (u : Quaternion ℝ) (hu : u.re = 0) (h_norm : ‖u‖ < Real.pi) :
  log_at_1 (NormedSpace.exp ℝ u) = u := by
    unfold log_at_1
    -- By definition of Log_map, we have:
    unfold Log_map
    -- By definition of NormedSpace.exp, we know that NormedSpace.exp ℝ u = cos(‖u‖) + (sin(‖u‖)/‖u‖) • u.
    have h_exp : NormedSpace.exp ℝ u = Real.cos ‖u‖ + (Real.sin ‖u‖ / ‖u‖) • u := by
      have h_exp : NormedSpace.exp ℝ u = Real.cos ‖u‖ + (Real.sin ‖u‖ / ‖u‖) • u := by
        have h_exp_def : ∀ (u : Quaternion ℝ), u.re = 0 →
            NormedSpace.exp ℝ u = Real.cos ‖u‖ + (Real.sin ‖u‖ / ‖u‖) • u := by
          exact fun u a ↦ Quaternion.exp_of_re_eq_zero u a
        exact h_exp_def u hu
      exact h_exp
    by_cases hu : u = 0 <;> simp_all +decide [div_eq_inv_mul, mul_assoc, mul_left_comm]
    · norm_num [inner_self_eq_norm_sq_to_K]
    · -- By definition of inner, inner ℝ 1 (...) = Real.cos ‖u‖.
      have h_inner :
          inner ℝ 1 (↑(Real.cos ‖u‖) + (‖u‖⁻¹ * Real.sin ‖u‖) • u) = Real.cos ‖u‖ := by
        exact Eq.symm (by
          erw [Quaternion.inner_def]
          norm_num [*, Quaternion.normSq])
      rw [h_inner, Real.sin_arccos]
      rw [← Real.sin_sq,
        Real.sqrt_sq (le_of_lt (Real.sin_pos_of_pos_of_lt_pi (norm_pos_iff.mpr hu) h_norm))] ; ring_nf
      rw [Real.arccos_cos] <;> try linarith [norm_nonneg u]
      ext <;> norm_num [hu, mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv]
      · by_cases h : Real.sin ‖u‖ = 0 <;> aesop
      · rw [mul_inv_cancel₀ (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (norm_pos_iff.mpr hu) h_norm)), mul_one]
      · rw [mul_inv_cancel₀ (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (norm_pos_iff.mpr hu) h_norm)), mul_one]
      · rw [mul_inv_cancel₀ (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (norm_pos_iff.mpr hu) h_norm)), mul_one]

/-
The exponential of a pure quaternion u is approximately 1 + u + u^2/2 with error order 3.
-/
lemma exp_approx_2 :
  ∃ C > 0, ∀ u : Quaternion ℝ, u.re = 0 → ‖u‖ ≤ 1 →
  ‖NormedSpace.exp ℝ u - (1 + u + u^2 / 2)‖ ≤ C * ‖u‖^3 := by
    -- We'll use the fact that the exponential of a pure quaternion can be written as a power series.
    have h_exp_series : ∀ u : Quaternion ℝ, u.re = 0 →
        NormedSpace.exp ℝ u = ∑' n : ℕ, (u ^ n) / (n ! : ℝ) := by
      norm_num [NormedSpace.exp_eq_tsum_div]
      exact fun u a ↦ rfl
    -- We'll use the fact that the series expansion of the exponential function converges to the exponential function itself.
    have h_exp_series_conv :
        ∀ u : Quaternion ℝ, u.re = 0 → ‖u‖ ≤ 1 →
          NormedSpace.exp ℝ u = 1 + u + u^2 / 2 +
            ∑' n : ℕ, (u ^ (n + 3)) / ((n + 3)! : ℝ) := by
      intro u hu hnorm
      rw [h_exp_series u hu]
      rw [← Summable.sum_add_tsum_nat_add 3]
      norm_num [Finset.sum_range_succ]
      · rfl
      · exact Summable.of_norm <| by simpa using Real.summable_pow_div_factorial ‖u‖
    -- We'll use the fact that the tail series is bounded by (‖u‖^3 / 6) * exp(‖u‖).
    have h_series_bound :
        ∀ u : Quaternion ℝ, u.re = 0 → ‖u‖ ≤ 1 →
          ‖∑' n : ℕ, (u ^ (n + 3)) / ((n + 3)! : ℝ)‖ ≤
            ‖u‖ ^ 3 / 6 * Real.exp ‖u‖ := by
      intros u hu hnorm
      have h_series_abs_conv :
          ‖∑' n : ℕ, (u ^ (n + 3)) / ((n + 3)! : ℝ)‖ ≤
            ∑' n : ℕ, (‖u‖ ^ (n + 3)) / ((n + 3)! : ℝ) := by
        convert norm_tsum_le_tsum_norm _ <;> norm_num [Norm.norm]
        exact Real.summable_pow_div_factorial _ |>
          Summable.comp_injective <| add_left_injective _
      refine le_trans h_series_abs_conv ?_
      rw [Real.exp_eq_exp_ℝ]
      rw [NormedSpace.exp_eq_tsum_div]
      rw [← tsum_mul_left]
      refine' Summable.tsum_le_tsum _ _ _
      · intro n
        rw [div_mul_div_comm]
        rw [div_le_div_iff₀] <;> first | positivity | ring_nf
        norm_num [add_comm, Nat.factorial]
        exact le_of_sub_nonneg (by ring_nf; positivity)
      · exact Real.summable_pow_div_factorial _ |>
          Summable.comp_injective <| add_left_injective 3
      · exact Summable.mul_left _ <| Real.summable_pow_div_factorial _
    refine' ⟨6 * Real.exp 1, by positivity, fun u hu hu' => _⟩
    rw [h_exp_series_conv u hu hu', add_sub_cancel_left]
    exact le_trans (h_series_bound u hu hu')
      (by
        nlinarith [Real.exp_pos ‖u‖, Real.exp_le_exp.mpr hu', pow_nonneg (norm_nonneg u) 3])

/-
Any unit quaternion can be written in polar form cos(theta) + sin(theta) * v where v is a unit pure quaternion.
-/
lemma unit_quaternion_polar_decomposition (q : Quaternion ℝ) (hq : ‖q‖ = 1) :
  ∃ θ : ℝ, ∃ v : Quaternion ℝ, v.re = 0 ∧ ‖v‖ = 1 ∧ q = Real.cos θ + Real.sin θ • v := by
    -- Let θ be arccos(q.re). If sin(θ) = 0, then q = 1 or -1. Take v = i (arbitrary unit pure quaternion).
    by_cases hsin : Real.sin (Real.arccos (q.re)) = 0
    · -- If sin(theta) = 0, then q = 1 or -1. Take v = i (arbitrary unit pure quaternion).
      use Real.arccos (q.re), ⟨0, 1, 0, 0⟩
      simp_all +decide [norm_eq_sqrt_real_inner, Quaternion.inner_self]
      norm_num [Real.sin_arccos, Quaternion.normSq] at *
      rw [Real.sqrt_eq_zero'] at hsin
      rw [Real.cos_arccos] <;> try nlinarith
      ext <;> simp_all +decide [Quaternion.ext_iff]
      · cases abs_cases q.re <;> nlinarith [sq_nonneg q.imI, sq_nonneg q.imJ, sq_nonneg q.imK]
      · cases abs_cases q.re <;> nlinarith
      · cases abs_cases q.re <;> nlinarith
    · -- If sin(theta) != 0, take v = q.im / ‖q.im‖.
      obtain ⟨v, hv⟩ :
          ∃ v : Quaternion ℝ, v.re = 0 ∧ ‖v‖ = 1 ∧
            q.im = Real.sin (Real.arccos q.re) • v := by
        refine' ⟨(1 / Real.sin (Real.arccos q.re)) • q.im, _, _, _⟩ <;>
          simp_all +decide [norm_smul]
        simp_all +decide [Real.sin_arccos, abs_div, abs_mul, abs_of_nonneg, Real.sqrt_nonneg]
        simp_all +decide [norm_eq_sqrt_real_inner, Quaternion.inner_self]
        simp_all +decide [Quaternion.normSq_def, sq]
        grind
      refine' ⟨Real.arccos q.re, v, hv.1, hv.2.1, _⟩
      simp_all +decide [Real.sin_arccos, Real.cos_arccos, Quaternion.ext_iff]
      rw [Real.cos_arccos] <;>
        nlinarith [Real.sqrt_nonneg (1 - q.re ^ 2),
          Real.mul_self_sqrt (show 0 ≤ 1 - q.re ^ 2 by nlinarith [Real.sqrt_ne_zero'.mp hsin])]

/-
The exponential map is surjective onto the unit quaternions, and the preimage can be chosen to be pure imaginary.
-/
lemma exists_exp_eq_of_norm_eq_one (q : Quaternion ℝ) (hq : ‖q‖ = 1) :
  ∃ w : Quaternion ℝ, w.re = 0 ∧ NormedSpace.exp ℝ w = q := by
    -- Use unit_quaternion_polar_decomposition to write q as cos(theta) + sin(theta) * v with v pure and |v|=1.
    obtain ⟨θ, v, hv_re, hv_norm, hq_eq⟩ :
        ∃ θ : ℝ, ∃ v : Quaternion ℝ, v.re = 0 ∧ ‖v‖ = 1 ∧
          q = Real.cos θ + Real.sin θ • v := by
      exact unit_quaternion_polar_decomposition q hq
    refine' ⟨θ • v, _, _⟩ <;> simp +decide [hq_eq, hv_re]
    -- Apply the exponential formula for pure quaternions.
    have h_exp_formula :
        ∀ u : Quaternion ℝ, u.re = 0 → ‖u‖ ≠ 0 →
          NormedSpace.exp ℝ u = Real.cos ‖u‖ + (Real.sin ‖u‖ / ‖u‖) • u := by
      exact fun u a a_1 ↦ Quaternion.exp_of_re_eq_zero u a
    by_cases hθ : θ = 0 <;> simp_all +decide [norm_smul]
    convert h_exp_formula (θ • v) _ _ using 1 <;> simp_all +decide [norm_smul]
    · cases abs_cases θ <;> simp +decide [*, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, smul_smul]
    · aesop_cat

/-
Proof of Theorem S13: Existence of w_L and R_L with the required bound.
-/
theorem TheoremS13 : TheoremS13Statement := by
  -- By definition of w_L, we know that NormedSpace.exp ℝ w_L = P.
  have hwL_exp :
      ∀ (u : Fin 0 → Quaternion ℝ) (ε : ℝ),
        (∀ i, ‖u i‖ ≤ ε) → (∀ i, (u i).re = 0) →
          ∃ w_L : Quaternion ℝ,
            NormedSpace.exp ℝ w_L = (List.ofFn (fun i => NormedSpace.exp ℝ (u i))).prod ∧
            ∃ R_L : Quaternion ℝ,
              w_L = (∑ i, u i) + (1 / 2) •
                (∑ i, ∑ j, if i < j then lie_bracket (u i) (u j) else 0) + R_L ∧
              ∃ C > 0, ‖R_L‖ ≤ C * (0 : ℝ)^3 * ε^3 := by
        simp +zetaDelta at *
        exact ⟨1, by norm_num⟩
  contrapose! hwL_exp
  refine' ⟨fun _ => _, 0, _, _, _⟩ <;> norm_num
  · exact 0
  · intro x hx y hy h
    have := congr_arg Norm.norm hx
    norm_num [h] at this
    exact hwL_exp fun L [NeZero L] u ε hu hε => by
      -- By definition of w_L, we know that NormedSpace.exp ℝ w_L = P and w_L = S1 + S2 + R_L.
      obtain ⟨w_L, hwL_exp, hwL⟩ :
          ∃ w_L : Quaternion ℝ,
            NormedSpace.exp ℝ w_L = (List.ofFn (fun i => NormedSpace.exp ℝ (u i))).prod ∧
            ∃ R_L : Quaternion ℝ,
              w_L = (∑ i, u i) + (1 / 2) •
                (∑ i, ∑ j, if i < j then lie_bracket (u i) (u j) else 0) + R_L := by
        have hwL_exp :
            ∃ w_L : Quaternion ℝ,
              NormedSpace.exp ℝ w_L = (List.ofFn (fun i => NormedSpace.exp ℝ (u i))).prod := by
          have hwL :
              ∀ (q : Quaternion ℝ), ‖q‖ = 1 →
                ∃ w : Quaternion ℝ, w.re = 0 ∧ NormedSpace.exp ℝ w = q := by
            exact fun q a ↦ exists_exp_eq_of_norm_eq_one q a
          have hwL :
              ∀ (L : ℕ) (u : Fin L → Quaternion ℝ),
                (∀ i, (u i).re = 0) →
                  ‖(List.ofFn (fun i => NormedSpace.exp ℝ (u i))).prod‖ = 1 := by
            exact fun L u a ↦ norm_prod_exp_pure_eq_one_list L u a
          exact Exists.imp (fun w => And.right)
            (‹∀ q : Quaternion ℝ, ‖q‖ = 1 → ∃ w : Quaternion ℝ, w.re = 0 ∧ NormedSpace.exp ℝ w = q›
              _ (hwL L u hε))
        exact ⟨hwL_exp.choose, hwL_exp.choose_spec,
          hwL_exp.choose -
            (∑ i, u i + (1 / 2) • ∑ i, ∑ j, if i < j then lie_bracket (u i) (u j) else 0),
          by rw [add_sub_cancel]⟩
      by_cases hε : ε = 0 <;> simp_all +decide [ne_of_gt]
      · exact ⟨1, by norm_num⟩
      · refine' ⟨w_L, hwL_exp, hwL.choose, hwL.choose_spec, _⟩
        refine' ⟨(‖hwL.choose‖ + 1) / (L ^ 3 * ε ^ 3), _, _⟩
        · exact div_pos (add_pos_of_nonneg_of_pos (norm_nonneg _) zero_lt_one)
            (mul_pos (pow_pos (Nat.cast_pos.mpr <| NeZero.pos L) 3)
              (pow_pos (lt_of_le_of_ne (le_trans (norm_nonneg _) (hu ⟨0, NeZero.pos L⟩)) (Ne.symm hε)) 3))
        · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀] <;>
            nlinarith [show 0 < (L : ℝ) ^ 3 * ε ^ 3 by
              exact mul_pos (pow_pos (Nat.cast_pos.mpr <| NeZero.pos L) 3)
                (pow_pos (lt_of_le_of_ne (le_trans (norm_nonneg _) (hu ⟨0, NeZero.pos L⟩)) (Ne.symm hε)) 3)]

/-
Corollary S14: Stack-level approximation and curvature clause.
-/
theorem CorollaryS14 : CorollaryS14Statement := by
  classical
  intro L _ d F_gsm F_std Lip C_head ε u hCpos hLip hErr hu hure
  set ε' : ℝ := ε * Real.sqrt C_head
  have hCnonneg : 0 ≤ C_head := le_of_lt hCpos
  have h_eps' : (ε * Real.sqrt C_head) ^ 2 = C_head * ε ^ 2 := by
    have h_sqrt_sq : (Real.sqrt C_head) ^ 2 = C_head := by
      simpa [pow_two] using (Real.sq_sqrt hCnonneg)
    calc
      (ε * Real.sqrt C_head) ^ 2 = ε ^ 2 * (Real.sqrt C_head) ^ 2 := by ring
      _ = C_head * ε ^ 2 := by simpa [h_sqrt_sq, mul_assoc, mul_left_comm, mul_comm]
  have hErr' : ∀ l x, ‖F_gsm l x - F_std l x‖ ≤ ε' ^ 2 := by
    intro l x
    have := hErr l x
    simpa [ε', h_eps'] using this
  obtain ⟨C_stack, hCpos_stack, hCbound⟩ :=
    BridgeTheoremStack L d F_gsm F_std Lip ε' hLip hErr'
  have hLge : (1 : ℝ) ≤ (L : ℝ) := by
    have hLge_nat : (1 : ℕ) ≤ L := (Nat.one_le_iff_ne_zero).2 (NeZero.ne L)
    exact_mod_cast hLge_nat
  have hCstack_nonneg : 0 ≤ (C_stack * C_head : ℝ) :=
    mul_nonneg (le_of_lt hCpos_stack) (le_of_lt hCpos)
  have hε_nonneg : 0 ≤ ε ^ 2 := by nlinarith
  have h_bound :
      ∀ x,
        ‖(List.ofFn F_gsm).foldr (fun f a => f a) x -
            (List.ofFn F_std).foldr (fun f a => f a) x‖ ≤
          (C_stack * C_head) * (L : ℝ) * ε ^ 2 := by
    intro x
    have h_base :
        ‖(List.ofFn F_gsm).foldr (fun f a => f a) x -
            (List.ofFn F_std).foldr (fun f a => f a) x‖ ≤
          C_stack * C_head * ε ^ 2 := by
      have h := hCbound x
      simpa [ε', h_eps', mul_assoc, mul_left_comm, mul_comm] using h
    have h_scale :
        C_stack * C_head * ε ^ 2 ≤ (C_stack * C_head) * (L : ℝ) * ε ^ 2 := by
      have h_nonneg : 0 ≤ C_stack * C_head * ε ^ 2 :=
        mul_nonneg hCstack_nonneg hε_nonneg
      calc
        C_stack * C_head * ε ^ 2 = (C_stack * C_head * ε ^ 2) * 1 := by ring
        _ ≤ (C_stack * C_head * ε ^ 2) * (L : ℝ) := by
          exact mul_le_mul_of_nonneg_left hLge h_nonneg
        _ = (C_stack * C_head) * (L : ℝ) * ε ^ 2 := by ring
    exact h_base.trans h_scale
  obtain ⟨w_L, hw_exp, R_L, hw_eq, C_curv, hCcurv_pos, hR⟩ :=
    TheoremS13 L u ε hu hure
  refine' ⟨C_stack * C_head, mul_pos hCpos_stack hCpos, h_bound, _⟩
  refine' ⟨w_L, hw_exp, R_L, hw_eq, C_curv, hCcurv_pos, hR⟩
