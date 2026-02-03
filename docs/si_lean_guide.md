# SI ↔ Lean Verification Guide

This guide is written for Nature editors, peer reviewers, and contributors who want a clear map from the
Supplementary Information (SI) statements to the Lean verification artifacts.

## What is formally verified?

The Lean package mechanizes the SI statements **S1–S14**, including:
- Head‑level Bridge Theorem (S4, in `Attention/Logits.lean`).
- Stack‑level Bridge Theorem clause (in `Gradients/Statements.lean` and proved in `Gradients/Proofs.lean`).
- Small‑angle/geometry lemmas, exp/log bounds, and gradient/curvature claims.

The Lean proofs are independent of the LaTeX derivations (they can deviate in proof technique), but the
**statements are aligned to the SI**. Where the SI introduces constants (e.g., error prefactors), the Lean
statements make those constants explicit.

## Mapping SI statements to Lean files

| SI Statement | Lean file(s) | Notes |
| --- | --- | --- |
| S1 (Sign invariance) | `RgatNaturePaper/Geometry/Basic.lean:39` | `sign_invariance` lemma. |
| S2 (Small-angle expansion) | `RgatNaturePaper/Geometry/SmallAngle.lean:177` (statement), `:182` (proof) | Includes explicit ε0 parameter. |
| S3 (Softmax stability) | `RgatNaturePaper/Gradients/Statements.lean:155` (statement), `RgatNaturePaper/Gradients/Proofs.lean:32` (proof) | Mean‑value/regularity machinery. |
| S4 (Bridge Theorem, head) | `RgatNaturePaper/Attention/Logits.lean:74` (statement block) | Softmax/logits + geometric → Euclidean limit. |
| S4 (Bridge Theorem, stack) | `RgatNaturePaper/Gradients/Statements.lean:110` (statement), `RgatNaturePaper/Gradients/Proofs.lean:113` (proof) | Explicit product constant; assumes Lip ≥ 1. |
| S5–S8 | `RgatNaturePaper/Gradients/Proofs.lean:257`, `:285`, `:274`, `:307` | Theorem S5, Corollary S6, Lemma S7, Corollary S8. |
| S9 (Gauge equivariance) | `RgatNaturePaper/Transformers/Statements.lean:33` (statement), `RgatNaturePaper/Gradients/Proofs.lean:364` (proof) | Statement + proof. |
| S10–S12 | `RgatNaturePaper/Gradients/Statements.lean:60`, `:71` and `RgatNaturePaper/Gradients/Proofs.lean:448`, `:500` | Gradient/BCH machinery. |
| S13 (Depth accumulation) | `RgatNaturePaper/Gradients/Statements.lean:87` (statement), `RgatNaturePaper/Gradients/Proofs.lean:673` (proof) | Explicit remainder bound. |
| S14 (Corollary) | `RgatNaturePaper/Gradients/Statements.lean:131` (statement), `RgatNaturePaper/Gradients/Proofs.lean:731` (proof) | Stack‑level approximation + curvature clause. |

## How to navigate the Lean package

Start with the umbrellas:

- `RgatNaturePaper/Geometry.lean`
- `RgatNaturePaper/Attention.lean`
- `RgatNaturePaper/Transformers.lean`
- `RgatNaturePaper/Gradients.lean`

Then drill down:

- Geometry and small‑angle lemmas: `RgatNaturePaper/Geometry/*`
- Softmax/logits and head‑level Bridge Theorem: `RgatNaturePaper/Attention/*`
- Stack‑level bound + gradient statements: `RgatNaturePaper/Gradients/*`

For a structural overview, see:
- `docs/structure/dependency_graph.md`
- `docs/structure/file_summaries.md`

## Reproducing formal checks

From the repo root:

```bash
lake build
```

This builds all Lean targets and replays every statement proof.

## Reviewer audit checklist (5 steps)

1. **Confirm SI mapping.** Use the SI ↔ Lean table above to locate the statement you care about.
2. **Inspect the statement.** Open the referenced `Statements.lean` file and verify the Lean statement matches the SI wording (constants and hypotheses explicit).
3. **Inspect the proof.** Jump to the corresponding proof in `Proofs.lean` (or the module listed) and skim the structure; comments call out nontrivial steps.
4. **Run the checker.** Execute `lake build` to replay all proofs with the pinned toolchain.
5. **Cross‑reference equations.** When in doubt, compare against the exact equation or theorem number in `docs/tex/si_rgat_nature.tex`.
