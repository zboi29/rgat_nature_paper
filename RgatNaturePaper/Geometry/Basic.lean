/-
Basic quaternionic geometry for RGAT.

Defines the sign-invariant similarity and geodesic distance on the unit
quaternions (S^3), together with Lemma S1 (sign invariance). These are the
geometric primitives for GSM logits and later approximation lemmas.
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
### Core definitions

`s_sim` is the absolute inner product, identifying antipodal points on S^3.
`d_geo` is the induced geodesic distance used in the SI.
-/

/-- Sign-invariant similarity. -/
noncomputable def s_sim (q k : Quaternion ℝ) : ℝ := |inner ℝ q k|

/-- Geodesic distance on S^3 induced by the inner product. -/
noncomputable def d_geo (q k : Quaternion ℝ) : ℝ := 2 * Real.arccos (s_sim q k)

/- Lemma S1: sign invariance under the Spin(3) double cover. -/
lemma sign_invariance (q k : Quaternion ℝ) (_hq : ‖q‖ = 1) (_hk : ‖k‖ = 1) :
  d_geo q k = d_geo (-q) k ∧ d_geo q k = d_geo q (-k) := by
    unfold d_geo
    unfold s_sim
    aesop
