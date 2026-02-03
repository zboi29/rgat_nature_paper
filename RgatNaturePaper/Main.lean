/-
Main entrypoint for RGAT Nature Paper formalization.
Imports umbrella modules that in turn pull in the refactored submodules:
- Geometry (basic defs + approximation/small-angle lemmas)
- Attention (softmax machinery + logits + S4 head-level bridge)
- Transformers (statement module)
- Gradients (statements + proofs)
-/
import RgatNaturePaper.Geometry
import RgatNaturePaper.Attention
import RgatNaturePaper.Transformers
import RgatNaturePaper.Gradients
