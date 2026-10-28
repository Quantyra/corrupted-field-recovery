# Source and authorship provenance

Historical repository: `Quantyra/quantyra-quantum-complexity`.
Pinned revision: `d2ae8c6fc275423c2276ba82644b8993660ec684` (28 October 2026).

| Historical path | Use in this package |
|---|---|
| `proofs/s173-corrupted-field-contractions-and-cost-2026-10-28.md` | R05-08 four-contraction proof, sampling argument, bounded discovery |
| `proofs/s173-phase-defect-tensors-and-complete-counts-2026-10-28.md` | Cubic imbalance and supported residual reconstruction; quadratic/quantum portions excluded |
| `src/corrupted_field_contractions.py` | Contraction and simultaneous balance construction |
| `src/cubic_centroid_descent.py` | Packed binary matrix conventions, nullspace and scalar-field module construction |
| `src/finite_field_descent.py` | Binary echelon and witness solving |
| `src/finite_field_acceptance.py` | Polynomial field arithmetic and irreducibility test |
| `src/field_defect_subspaces.py` | Candidate generator certification |
| `src/phase_defect_tensors.py` | Cubic imbalance image and whole-coefficient fitting |

The standalone source adapts these elementary routines and reconstructs the cubic-only interface. It imports no historical Python module at runtime. Full phase recovery, native circuits, output counting and their external backends are not copied into this package. Historical evidence remains at its original paths. The source tree at the pinned revision did not contain a root license; publication and packaging of this Quantyra work are authorized by its sponsor. The standalone package states its own licenses explicitly.

The earlier cubic-only side audit had no saved script or standalone proof. The present manuscript and test suite are newly saved artifacts and have their own source hashes. Their evidence is not retroactively attributed to the earlier conversation.

Author: Daniel Eric Fredriksen, Quantyra Inc, as established in the existing Quantyra publication metadata (`quantyra-null-cone-lean/CITATION.cff` and `.zenodo.json`). No ORCID is inferred. Codex assisted with reconstruction, software, tests, Lean development and writing. Three separate AI-model review passes (GPT-6 Astra, GPT-6.1 Terra, GPT-6.1 Sol), their scope and feedback dispositions are saved in `docs/reviews`; no independent human peer review is claimed.

Software, tests and Lean files: Apache-2.0, see `LICENSE`. Manuscript: CC-BY-4.0, see `LICENSES/CC-BY-4.0.txt`. Third-party Lean dependencies retain their original licenses and pinned revisions. No third-party article PDFs are redistributed.
