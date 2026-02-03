# RGAT Lean File Summaries

- `docs/si_lean_guide.md` — SI-to-Lean mapping and reviewer navigation guide.
- `RgatNaturePaper/Main.lean` — Main entrypoint importing umbrella modules.
- `RgatNaturePaper/Geometry.lean` — Umbrella for geometry-related submodules.
- `RgatNaturePaper/Geometry/Basic.lean` — Core geometry defs (`s_sim`, `d_geo`) and sign invariance.
- `RgatNaturePaper/Geometry/ExpApprox.lean` — exp/approximation lemmas (cos/sinc bounds, inner expansion).
- `RgatNaturePaper/Geometry/SmallAngle.lean` — arccos/inner bounds, small‑angle expansion, and Lemma S2 alias.
- `RgatNaturePaper/Attention.lean` — Umbrella for attention submodules.
- `RgatNaturePaper/Attention/Softmax.lean` — softmax definition, derivatives, Jacobian bounds, norm lemmas.
- `RgatNaturePaper/Attention/Logits.lean` — pure‑quaternion embedding, logits, S4 bridge theorem, logits approximations.
- `RgatNaturePaper/Transformers.lean` — Umbrella for transformer statements.
- `RgatNaturePaper/Transformers/Statements.lean` — Theorem S9 statement.
- `RgatNaturePaper/Gradients.lean` — Umbrella for gradients.
- `RgatNaturePaper/Gradients/Statements.lean` — Statements for S10–S14 and stack‑level Bridge Theorem clause (explicit constants).
- `RgatNaturePaper/Gradients/Proofs.lean` — Proofs for S5–S12, Lemma S3, S9–S11, plus gradient lemmas.
