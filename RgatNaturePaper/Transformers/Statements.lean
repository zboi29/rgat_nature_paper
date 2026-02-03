/-
Transformer-level statements.

This module records the SI statement for gauge equivariance (Theorem S9),
formalized as a property of GSM attention under left multiplication by a unit
quaternion and an orthogonal representation on values.
-/
import Mathlib
import RgatNaturePaper.Attention

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 400000
set_option maxRecDepth 3000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-
### SI Theorem S9 (Gauge equivariance)
-/

/-
Theorem S9: Gauge equivariance of GSM attention. If queries and keys are transformed by left multiplication by a unit quaternion g, and values are transformed by an orthogonal representation L(g), then the output transforms by L(g).
-/
def TheoremS9Statement : Prop :=
  ∀ (T d : ℕ) [NeZero T] (Q K : Fin T → Quaternion ℝ) (v : Fin T → Fin d → ℝ) (tau : ℝ) (g : Quaternion ℝ) (L : (Fin d → ℝ) → (Fin d → ℝ)),
  let Q' := fun i => g * Q i
  let K' := fun j => g * K j
  let P := fun i => softmax (fun j => - (1 / (2 * tau)) * (d_geo (Q i) (K j))^2)
  let P' := fun i => softmax (fun j => - (1 / (2 * tau)) * (d_geo (Q' i) (K' j))^2)
  let y := fun i => ∑ j, P i j • v j
  let y' := fun i => ∑ j, P' i j • L (v j)
  (‖g‖ = 1) →
  (∀ x, ‖L x‖ = ‖x‖) →
  (IsLinearMap ℝ L) →
  (∀ i, y' i = L (y i))
