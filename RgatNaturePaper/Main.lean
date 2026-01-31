/-
Main entrypoint for RGAT Nature Paper formalization.
Splits content into four logical modules:
- Geometry (core analytic lemmas)
- Attention (softmax/GSM definitions & statements)
- Transformers (S5–S9 and related corollaries)
- Gradients (S10–S14 and gradient-related results)
-/
import RgatNaturePaper.Geometry
import RgatNaturePaper.Attention
import RgatNaturePaper.Transformers
import RgatNaturePaper.Gradients
