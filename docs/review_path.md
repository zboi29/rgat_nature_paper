# Review Path (5–10 minutes)

This page is a short, practical path for editors and reviewers to verify the
formal claims without needing deep Lean expertise.

## 1) Confirm statement coverage (1–2 minutes)

Open `docs/si_lean_guide.md` and scan the SI statement table to confirm that
S1–S14 are mapped to Lean files.

## 2) Check the core statements (2–3 minutes)

Spot‑check a few anchor statements and note their file/line locations:

- **S1 (Sign invariance)**: `RgatNaturePaper/Geometry/Basic.lean:39`
- **S2 (Small‑angle expansion)**: `RgatNaturePaper/Geometry/SmallAngle.lean:177` (statement) and `:182` (proof)
- **S4 (Bridge Theorem, head)**: `RgatNaturePaper/Attention/Logits.lean:74` (statement block)
- **S4 (Bridge Theorem, stack clause)**: `RgatNaturePaper/Gradients/Statements.lean:110` (statement) and `RgatNaturePaper/Gradients/Proofs.lean:113` (proof)
- **S13 (Depth accumulation)**: `RgatNaturePaper/Gradients/Statements.lean:87` (statement) and `RgatNaturePaper/Gradients/Proofs.lean:673` (proof)
- **S14 (Corollary)**: `RgatNaturePaper/Gradients/Statements.lean:131` (statement) and `RgatNaturePaper/Gradients/Proofs.lean:731` (proof)

## 3) Run the formal checker (2–3 minutes)

From repo root:

```bash
lake update
lake exe cache get
lake build
```

If `lake build` succeeds, the Lean kernel has verified all statements.

## 4) Cross‑reference SI equations (optional)

Open `docs/tex/si_rgat_nature.tex` and confirm that the Lean statements match the
exact theorem/lemma formulations (constants and hypotheses explicit).

