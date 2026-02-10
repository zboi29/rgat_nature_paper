# RGAT Lean Module Dependency Graph

This document summarizes the Lean module layout and dependencies after refactoring.

## High-level structure

```
RgatPaperProofs.Main
  -> RgatPaperProofs.Geometry
     -> RgatPaperProofs.Geometry.Basic
     -> RgatPaperProofs.Geometry.ExpApprox
     -> RgatPaperProofs.Geometry.SmallAngle (imports Basic, ExpApprox)
  -> RgatPaperProofs.Attention
     -> RgatPaperProofs.Attention.Softmax
     -> RgatPaperProofs.Attention.Logits (imports Geometry, Attention.Softmax)
  -> RgatPaperProofs.Transformers
     -> RgatPaperProofs.Transformers.Statements
  -> RgatPaperProofs.Gradients
     -> RgatPaperProofs.Gradients.Statements (imports Attention, Transformers)
     -> RgatPaperProofs.Gradients.Proofs (imports Gradients.Statements, Attention, Transformers)
```

## Lean package details

- **Package name:** `rgat_paper_proofs`
- **Lean toolchain:** `leanprover/lean4:v4.24.0`
- **Core dependency:** `mathlib` pinned at `v4.24.0`
- **Default target:** `RgatPaperProofs`

See `lakefile.toml` and `lean-toolchain` for authoritative configuration.

## Notes

- `RgatPaperProofs.Geometry.*` contains all geometric and small-angle approximation lemmas (including Lemma S2 alias).
- `RgatPaperProofs.Attention.*` contains softmax machinery, logits/embedding lemmas, and the S4 head-level bridge theorem.
- `RgatPaperProofs.Transformers.*` currently holds transformer statement definitions.
- `RgatPaperProofs.Gradients.*` separates statements from proofs for gradient/optimization theorems, including the stack-level Bridge Theorem clause with explicit constants.
- For SI statement mapping and reviewer guidance, see `docs/si_lean_guide.md`.
