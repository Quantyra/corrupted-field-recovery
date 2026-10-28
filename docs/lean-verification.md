# Lean verification checkpoint, 28 October 2026

The algebraic two-translate defect-image argument is compiled and kernel checked. **The complete manuscript theorem is not certified.** The proof of the field-identification and randomized recovery algorithm, its probabilities, certificate checker and costs remains unfinished.

Lean 4.30.0, commit `d024af099ca4bf2c86f649261ebf59565dc8c622`; mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`. All dependency revisions are pinned in `lake-manifest.json`.

| Export in namespace `CorruptedFieldRecovery` | Proved scope | Axioms |
|---|---|---|
| `imbalance_add` | The displacement distributes over addition of trilinear forms | `propext`, `Quot.sound` |
| `balanced_cancels` | A tensor balanced by the operator disappears under displacement | `propext`, `Quot.sound` |
| `imbalance_mode_le` | The displaced third mode image is contained in the original mode image | `propext`, `Quot.sound` |
| `two_translate_modeImage` | Equality of mode images for a supported pullback when the joint observation map is onto | `propext`, `Quot.sound` |
| `recovery_modeImage` | Image recovery after adding a balanced tensor, under the same joint condition | `propext`, `Quot.sound` |
| `joint_surjective_of_disjoint_duals` | Two surjective maps with disjoint dual-image spaces have a surjective joint map | `propext`, `Classical.choice`, `Quot.sound` |
| `two_translate_of_disjoint` | The supported image is recovered for an invertible action when the original and translated dual-image support spaces are disjoint | `propext`, `Classical.choice`, `Quot.sound` |

The last theorem derives the joint-surjectivity requirement through the preceding theorem. It does not assume recovered-image equality. These algebraic statements are proved over arbitrary fields, using a difference operator; in characteristic two that difference equals the manuscript's sum. They do not assume or prove the full main recovery conclusion.

Executed `lake build CorruptedFieldRecovery`: exit 0, 1,646 jobs. Executed `lake env lean checks/Audit.lean`: exit 0. The audit prints full types for the selected image theorems and all seven transitive axiom reports. Source screening found no `sorry`, `admit`, new axiom, `native_decide`, or unsafe declaration in the project proof files. The reports contain only the standard foundations shown above. Exact source hashes and raw successful logs are in `artifacts/lean-checks.json`, `lean-build.log` and `lean-audit.log`.

All builds ran locally on Windows. The local package directory reused the existing pinned mathlib cache via a junction; that junction is untracked and no shared tracked dependency source was modified. A fresh checkout uses the pinned dependencies and focused cache commands in the README. No cloud execution or spend occurred.

The [coverage inventory](../formal/coverage.json) is the authoritative list of unfinished manuscript obligations. The readiness checker detects the missing complete proof and does not equate this successful intermediate build with publication readiness. Python remains separately tested, not formally verified.

Remaining to-do list: concrete binary/field model; four-contraction theorem; finite-field and conditional sampling bounds; bounded mathematical constructor; complete coefficient-checker soundness; charged costs; final main-theorem assembly and scope audit.
