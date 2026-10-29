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

The post-publication cross-provider review prompted an explicit inventory split: `two_translate_image` is marked `abstract_kernel_only`, while the required `two_translate_bridge` remains unformalized. The latter must establish the concrete binary/support/mode-image correspondence, the manuscript's weaker restricted-dual-injectivity hypothesis, and the coefficient-slice bridge. Seven abstract declarations being proved does not mean that exact manuscript lemma is fully covered.

Executed `lake build CorruptedFieldRecovery`: exit 0, 1,646 jobs. Executed `lake env lean checks/Audit.lean`: exit 0. The audit prints full types for the selected image theorems and all seven transitive axiom reports. Source screening found no `sorry`, `admit`, new axiom, `native_decide`, or unsafe declaration in the project proof files. The reports contain only the standard foundations shown above. Exact source hashes and raw successful logs are in `artifacts/lean-checks.json`, `lean-build.log` and `lean-audit.log`.

All builds ran locally on Windows. The local package directory reused the existing pinned mathlib cache via a junction; that junction is untracked and no shared tracked dependency source was modified. A fresh checkout uses the pinned dependencies and focused cache commands in the README. No cloud execution or spend occurred.

The [coverage inventory](../formal/coverage.json) is the authoritative list of unfinished manuscript obligations. The default readiness checker validates a preprint with accurate partial-formalization disclosure. Its `--require-complete-lean` mode additionally requires every manuscript obligation and the final theorem. An intermediate build cannot satisfy that stricter gate. Python remains separately tested, not formally verified.

Remaining to-do list: concrete binary/field model; four-contraction theorem; finite-field and conditional sampling bounds; bounded mathematical constructor; complete coefficient-checker soundness; charged costs; final main-theorem assembly and scope audit.


## GCP coefficient-semantics increment, 29 October 2026 UTC

The exact-source GCP run `cfr-certificate-soundness-dev02-20261029T045232Z-48c5f2` passed the focused build, five-declaration full-type/transitive-axiom audit and zero-new-warning gate. Source SHA-256 for `CertificateSoundness.lean` is `4dcc2a71b47b6bbd5042dfa879e3aae4d6a14e0145956706c2b252e29fb5b610`; the pinned toolchain and dependencies are unchanged. Raw logs, emitted types and hashed terminal collection are retained under `evidence/gcp/` at that run identity. The preceding failed source and two prelaunch Windows transport failures remain preserved.

Root inspected the actual types and accepted the narrow semantic result: for an alternating binary tensor input and a supplied `RepresentationPayload`, acceptance of the increasing-basis coefficient comparisons implies equality with the payload tensor on every vector triple. The rank parameter is unrestricted. The payload supplies its support data, support-dimension bound and alternating summands as fields. The checker uses noncomputable classical `decide`; this result establishes coefficient-to-tensor equality, not an executable checker, validated trace-determinant structure, complete certificate verification, constructor correctness or any operational cost bound. All five audited declarations use only `propext`, `Classical.choice` and `Quot.sound`.

Remaining to-do list: complete concrete field/certificate validation and executable checking; original recovery constructor, finite probability estimates, charged time/space bounds and end-to-end theorem audit.
