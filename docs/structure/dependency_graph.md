# RGAT Lean Module Dependency Graph

This document summarizes the Lean module layout and dependencies after refactoring.

## High-level structure

```
RgatNaturePaper.Main
  -> RgatNaturePaper.Geometry
     -> RgatNaturePaper.Geometry.Basic
     -> RgatNaturePaper.Geometry.ExpApprox
     -> RgatNaturePaper.Geometry.SmallAngle (imports Basic, ExpApprox)
  -> RgatNaturePaper.Attention
     -> RgatNaturePaper.Attention.Softmax
     -> RgatNaturePaper.Attention.Logits (imports Geometry, Attention.Softmax)
  -> RgatNaturePaper.Transformers
     -> RgatNaturePaper.Transformers.Statements
  -> RgatNaturePaper.Gradients
     -> RgatNaturePaper.Gradients.Statements (imports Attention, Transformers)
     -> RgatNaturePaper.Gradients.Proofs (imports Gradients.Statements, Attention, Transformers)
```

## Lean package details

- **Package name:** `rgat_nature_paper`
- **Lean toolchain:** `leanprover/lean4:v4.24.0`
- **Core dependency:** `mathlib` pinned at `v4.24.0`
- **Default target:** `RgatNaturePaper`

See `lakefile.toml` and `lean-toolchain` for authoritative configuration.

## Notes

- `RgatNaturePaper.Geometry.*` contains all geometric and small-angle approximation lemmas.
- `RgatNaturePaper.Attention.*` contains softmax machinery, logits/embedding lemmas, and the S4 head-level bridge theorem.
- `RgatNaturePaper.Transformers.*` currently holds transformer statement definitions.
- `RgatNaturePaper.Gradients.*` separates statements from proofs for gradient/optimization theorems.
