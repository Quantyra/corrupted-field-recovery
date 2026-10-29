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


## GCP hidden-input transport increment, 29 October 2026 UTC

The exact-source GCP run `cfr-binary-field-transport-dev02-20261029T045909Z-4b7bae` passed the focused build, three-declaration full-type/transitive-axiom audit and zero-new-warning gate. Source SHA-256 for `BinaryFieldTransport.lean` is `053a8a6e34e5ef576604aa1b8f1b329577f638153096d7ce0517240913d02888`. All three declarations use only `propext`, `Classical.choice` and `Quot.sound`. The existing terminal archive was recovered after a local transport process crash, verified against its remotely printed SHA-256 and every terminal stage-log hash, and retained alongside the failed transport receipt; the compiler was not rerun.

Root inspected the source and exact emitted types and accepted the narrow transport theorem: with an explicit prime-field-linear hidden input equivalence, finite characteristic-two field, sampled field basis, nonzero coefficient and a generating fourth coordinate, actual hidden-input four-form balance holds exactly for the transported scalar actions `x mapped to iota.symm (k smul iota x)`. The separate finrank conjunct concerns the existing coordinate scalar-map range. This increment does not establish the physical balance-space finrank, clean-sample conditions, hidden-field discovery, complete S009 or the complete recovery theorem.

Remaining to-do list: physical balance-space and input-encoding bridges; clean sampling, finite-field probability bounds, verified constructor and executable certificate validation; charged costs and the end-to-end theorem audit.


## GCP bridged array-equality gate, 29 October 2026 UTC

The exact-source GCP run `cfr-executable-certificate-dev03-20261029T055231Z-8a3f31` passed its focused build, seven-declaration untruncated type/transitive-axiom audit and zero-warning gate. Source SHA-256 for `ExecutableCertificate.lean` is `a754b12ac17bfee8c7a76ec83ab41f545cdce4dd18cfa8a2b65918fb62e818d6`. Exact source, prior failed attempts, raw logs and hashed terminal collection remain under `evidence/gcp/`. The audit reports only `propext`, `Classical.choice` and `Quot.sound`.

Root inspected the source and emitted types and accepted only this narrow result: finite ordered-array equality, after the four length checks, implies equality of every tensor coefficient and then every vector triple under the explicit tensor-array bridge fields. The checker reads the finite arrays; its input structures also contain semantic tensors and proof fields. The represented array and its bridge are supplied. Acceptance does not compute or validate the candidate sum, residual support or finite-field representation from raw data. It does not establish a complete executable certificate validator, constructor correctness or cost bounds.

Remaining to-do list: derive and validate the representation and tensor-array bridges from raw finite data; complete support/field validation, sampling and constructor proofs, charged costs and the end-to-end theorem audit.


## GCP clean-subspace counts, 29 October 2026 UTC

The exact-source GCP run `cfr-sampling-counts-dev04-20261029T060817Z-627c49` passed its focused build, two-declaration untruncated type/transitive-axiom audit and zero-warning gate. Source SHA-256 for `SamplingCounts.lean` is `9bd1e5bc62c1302b0a4e65bd010f436386f96e24891e7f005c854d54d4691864`. Exact inputs, preceding failed attempts, raw logs and hashed terminal collection remain under `evidence/gcp/`. Both declarations report only `propext`, `Classical.choice` and `Quot.sound`.

Root accepted the exact narrow statements: a surjective binary-linear map between finite-dimensional spaces of dimensions n and r has kernel cardinality 2^(n-r), and four choices from an arbitrary finite subset A give |A|^4 clean words. The kernel need not be linear over the hidden extension field. The second statement is a generic finite-set count. Neither theorem yet connects the manuscript's actual support promise to an independent uniform sampler or derives the clean-sampling probability, field-generation bounds, success amplification or complete S010.

Remaining to-do list: instantiate the support-kernel count and derive the actual finite sampling ratio; prove field-generation/translate estimates and bounded amplification; complete constructor/certificate validation, charged costs and final theorem assembly.


## GCP physical four-word clean counts, 29 October 2026 UTC

The exact-source GCP run `cfr-sampling-counts-dev08-20261029T064827Z-3ebddf` passed its focused build, four-declaration untruncated type/transitive-axiom audit and zero-warning gate. Source SHA-256 for `SamplingCounts.lean` is `22510a882dfc9a5c69a6d3f4c904c33e171c76beeb5ffcdd7e41b566f28eab05`. Earlier failed extensions and the local launch transport crash remain preserved. Observation and collection recovered this same launched run; the compiler was not repeated. All four audited declarations report only `propext`, `Classical.choice` and `Quot.sound`.

Root accepted the precise new conjunction: for a surjective binary-linear support map from `BinaryVector n` to `BinaryVector r`, with r <= R, the number of four-word tuples all in its kernel is 2^(4(n-r)), and that count multiplied by 2^(4R) is at least the number of all four-word tuples. The count uses the physical binary input space and does not assume extension-field linearity. This is an exact finite-count bound. The formal statement does not define an actual random-tape measure or establish conditional basis/generator events, a successful recovery trial, amplification or complete S010.

The guarded batch shutdown `2dc644` preserved every launched outcome, verified the task lock and absence of competing workloads or Lean/Lake processes, removed task-only external egress and verified the dedicated builder `TERMINATED` at 2026-10-29 07:01:38 UTC. Its persistent disk and compiled cache remain retained. Exact shutdown/cache receipts are alongside the dev08 evidence; no live compiler or queued capture remains.

Remaining to-do list: connect the support-map count to actual uniform independent tape sampling; prove the remaining conditional finite-field and translate estimates, trial success and amplification; finish constructor/certificate validation, charged costs and the final theorem audit.
