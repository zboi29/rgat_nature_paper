# RGAT Lean File Summaries

- `docs/si_lean_guide.md` — SI-to-Lean mapping and reviewer navigation guide.
- `RgatPaperProofs/Main.lean` — Main entrypoint importing umbrella modules.
- `RgatPaperProofs/Geometry.lean` — Umbrella for geometry-related submodules.
- `RgatPaperProofs/Geometry/Basic.lean` — Core geometry defs (`s_sim`, `d_geo`) and sign invariance.
- `RgatPaperProofs/Geometry/ExpApprox.lean` — exp/approximation lemmas (cos/sinc bounds, inner expansion).
- `RgatPaperProofs/Geometry/SmallAngle.lean` — arccos/inner bounds, small‑angle expansion, and Lemma S2 alias.
- `RgatPaperProofs/Attention.lean` — Umbrella for attention submodules.
- `RgatPaperProofs/Attention/Softmax.lean` — softmax definition, derivatives, Jacobian bounds, norm lemmas.
- `RgatPaperProofs/Attention/Logits.lean` — pure‑quaternion embedding, logits, S4 bridge theorem, logits approximations.
- `RgatPaperProofs/Transformers.lean` — Umbrella for transformer statements.
- `RgatPaperProofs/Transformers/Statements.lean` — Theorem S9 statement.
- `RgatPaperProofs/Gradients.lean` — Umbrella for gradients.
- `RgatPaperProofs/Gradients/Statements.lean` — Statements for S10–S14 and stack‑level Bridge Theorem clause (explicit constants).
- `RgatPaperProofs/Gradients/Proofs.lean` — Proofs for S5–S12, Lemma S3, S9–S11, plus gradient lemmas.
