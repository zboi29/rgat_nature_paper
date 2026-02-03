/-
Gradient-flow statements for RGAT.

Defines the core geometric objects (log map, energy) and the formal statements
for SI Theorems S10–S14. Proofs live in `Gradients/Proofs.lean`.
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
### Preliminaries

We use quaternions as a real inner product space, and define the principal
logarithm map `Log_map` and the energy function `energy_f`.
-/

/-
Check: `Quaternion ℝ` has the expected inner product structure.
-/
#synth InnerProductSpace ℝ (Quaternion ℝ)

/-
Principal log map and energy function:
`Log_map` maps a pair `(q, r)` to the tangent at `q` pointing toward `r`, and
`energy_f` is `1/2 * d_geo(q, r)^2` as in the SI.
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
