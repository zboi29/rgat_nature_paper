/-
Main entrypoint for RGAT Paper Proofs formalization.
Imports umbrella modules that in turn pull in the refactored submodules:
- Geometry (basic defs + approximation/small-angle lemmas)
- Attention (softmax machinery + logits + S4 head-level bridge)
- Transformers (statement module)
- Gradients (statements + proofs)
-/
import RgatPaperProofs.Geometry
import RgatPaperProofs.Attention
import RgatPaperProofs.Transformers
import RgatPaperProofs.Gradients
