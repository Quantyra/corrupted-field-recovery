# Sol adversarial manuscript and publication review

Date: 28 October 2026. Reviewer: GPT-6.1 Sol, the model identity assigned to this independent review pass. Technical baseline: `e7fa570ec7190d7a1c1f3a7c08ee91bc476fdc29`. This is AI-assisted internal review, not independent human peer review, journal acceptance, formal certification, or a priority clearance.

## Assessment

I found no mathematical counterexample or substantive correctness fault in the stated bounded compatible-recovery theorem. The main algebraic lemmas, conditional sampling argument, certificate meaning, amplification, and conservative cost envelopes fit together. Publication as a preprint explicitly disclosing partial Lean coverage is reasonable after ordinary package validation and the release-state reconciliation below. Complete Lean certification is not a prerequisite under the latest user instruction supplied to this review.

There is one concrete release-process conflict to correct before publication: the baseline still asserts and enforces the superseded Lean-before-release dependency. Two mathematical exposition improvements and one attribution improvement are advisable; none changes the theorem or demands completion of Lean before the preprint.

## Independence, scope, and checks

I read the required planning README, protocol, handoff, S002, and S004, then read `manuscript/main.tex` in full before reading any earlier technical audit conclusions. I did not consult other agents' review reports. I inspected `src/recovery.py`, `tests/check_recovery.py`, the saved Python/PDF/Lean receipts, `formal/coverage.json`, both Lean proof modules, `docs/lean-verification.md`, `tools/check_release_readiness.py`, README/build instructions, and `CITATION.cff`. I confirmed HEAD was the baseline when starting; this report makes no changes to shared code, manuscript, or planning.

I independently reran the complete finite Python checks locally with Python 3.14.7, exit 0, 20.385 seconds reported by the suite. The four recovery cases reproduced the recorded 1, 1574, 1, and 1 attempted trials. All 200 probability cases, nine field identifications, 104 image-recovery cases, negative control, altered certificates/tensor checks, malformed inputs, and exact bounded-failure assertions passed. The source hashes printed by this run matched the saved baseline receipt:

- `src/recovery.py`: `0c54ec4e33bb02e3eda054a2efb3360b8c537468be28ab09836e360617bf5617`.
- `tests/check_recovery.py`: `e4fd6928d2d3ee7f0f38f13462786480c8c3b0267239f234a9cf15516bd14bd1`.

To preserve the shared receipt, execution used an absolute `runpy` path and intercepted `pathlib.Path.write_text` with `unittest.mock.patch`. The interpreter was `C:/Users/dfred/AppData/Local/Google/Cloud SDK/google-cloud-sdk/platform/bundledpython/python.exe`; this was a local Python process, with no cloud execution or spend. The command body was:

```python
import runpy
from pathlib import Path
from unittest.mock import patch
ns = runpy.run_path(str(Path('tests/check_recovery.py').resolve()))
with patch('pathlib.Path.write_text', return_value=0):
    ns['main']()
```

The suite's printed `command` field is hardcoded to its ordinary documented command; the code above describes the actual review invocation. An initial direct `python` attempt hit the Windows execution alias. A first `runpy` attempt using a relative path ran the assertions but failed while preparing source hashes; using the absolute path corrected that harness issue. No new machine-readable receipt was saved or claimed. This report is the saved review record of the successful rerun.

I browsed primary sources for the focused comparison. I did not rebuild Lean, rebuild/render the PDF, validate Zenodo state, or perform publication operations. Existing successful build/visual-inspection receipts were inspected, not represented as newly repeated checks.

## Ranked findings

### F1 — Medium, release-blocking process inconsistency: obsolete formal-completion gate

Locations: `manuscript/main.tex:414`; `README.md:34`, `README.md:47`; `manuscript/README.md:11`; `tools/check_release_readiness.py:18`; `docs/lean-verification.md:23`.

The paper says release remains pending Lean certification, while the readiness script unconditionally fails when `coverage.complete` is false and when unfinished formal obligations remain. These statements conflict with the latest user direction to publish the DOI before completing Lean. The formal inventory itself correctly remains incomplete and must not be changed to a false completed status.

Suggested change: describe this as the first preprint with partial formal verification. Separate publication-package readiness from complete-formal-certification readiness, retaining the stricter check for the latter. A truthful release check should require current executable/PDF evidence and accurate partial-coverage disclosure, while reporting unfinished Lean obligations separately. Replace the final manuscript sentence with wording such as: “This preprint includes partial Lean verification of the defect-image argument; complete formal certification remains future work.” Update the date/version/citation metadata to the actual release state and verify the eventual archive/DOI. This is a documentation and control reconciliation, not a request for another permission gate.

### F2 — Low, recommended proof clarification: transport to the reconstructed coordinates

Locations: `manuscript/main.tex:270` and `manuscript/main.tex:284` (the module-basis justification and the good-trial coefficient-fit argument).

The text proves that the recognized embedded algebra is a field and that greedy module vectors yield a basis, then asserts that the coefficient system contains the original compatible tensor. This is correct, but the field/coordinate transport is implicit.

Suggested insertion: on a good trial, the map from `F_2[X]/(p)` to the planted field sending `X` to the sampled generator identifies the two scalar actions. The constructed physical basis therefore gives coordinates linear over this identified field. Changing a three-dimensional field basis multiplies the determinant by a nonzero scalar, and field isomorphisms preserve the absolute trace. Consequently the original compatible tensor is one of the constructed trace-determinant columns' linear combinations with some nonzero coefficient `c'`. This is a useful explicit bridge for both readers and future Lean formalization. It is not an identified false premise or a reason to defer a partial-formalization preprint.

### F3 — Low, recommended terminology clarification: the displaced tensor need not be alternating in all slots

Locations: `manuscript/main.tex:132` and `manuscript/main.tex:144`–`manuscript/main.tex:168`.

The third mode-image definition applies to arbitrary trilinear tensors, but only alternating tensors have the asserted common mode image/minimal common support interpretation. `D_T E` is alternating in its first two slots in characteristic two; it need not be alternating in all three. The proof and implementation correctly use only its third mode image, so this causes no correctness defect.

Suggested insertion after the displacement definition: “The displacement is not required to be alternating in all three arguments; throughout, `W(D_T E)` denotes only its third mode image.” Keep the smallest-common-support claim restricted to the original alternating error `E`.

### F4 — Low, optional attribution expansion: follow Hora's explicit trace-derived-form precursor

Location: `manuscript/main.tex:333`–`manuscript/main.tex:339` and bibliography.

Hora's 2019 introduction identifies ring forms as generalizing earlier trace-derived forms and cites his 2012 paper, *Autotopisms and Isotopisms of Trilinear Alternating Forms*, Communications in Algebra 40(4), 1438–1455. Adding this direct precursor would improve attribution to the uncorrupted structure. The current manuscript already disclaims originating ring forms and does not assert priority, so its omission is not presently a release blocker. I inspected the 2012 publisher abstract/metadata, not its full proof, and make no assertion that it subsumes the corrupted-recovery theorem. Sources: [Hora 2019](https://ijpam.uniud.it/online_issue/201941/55-Jan%20Hora.pdf), [Hora 2012 publisher record](https://www.tandfonline.com/doi/abs/10.1080/00927872.2011.551899).

## Mathematical challenges resolved by inspection

- Four contractions: radical preservation forces three diagonal binary maps; the three off-diagonal adjoint identities force them equal and self-adjoint. A generating fourth coordinate forces commutation with all field scalars. The balance space is a linear space until field recognition proves the required algebra structure; the algorithm does not assume arbitrary noisy balance spaces are fields.
- Sampling: conditional cleanliness gives uniform samples in the annihilator, not uniform field coordinates. The sequential forbidden-set and fiber estimates remain valid for every earlier basis triple. The independently drawn scalar is uniform in the correct balance space even though the chosen basis depends on earlier draws. The union bound for translated support includes zero and other bad scalars. The inequalities at `s >= 2R+5` imply the displayed lower bound, and `exp(-h) <= 2^(-h)` is in the correct direction.
- Defect/certificate: the onto joint observation map isolates any original contracted error covector. Only the original alternating error needs the common-support argument. All accepted output is independently checked as a compatible representation, with no claimed planted uniqueness. Under a good trial, a nonzero trace-determinant has full third mode image, so no nonzero compatible tensor lies in the recovered small-support error subspace; rejecting a zero compatible coefficient does not discard the good representation.
- Construction/costs: the power-basis tests and irreducible relation make the recovered scalar algebra a degree-`s` field. Greedy module construction is valid over that field. Dense coefficient verification is sufficient by multilinearity/alternation. Binary elimination and polynomial-representative arithmetic fit the deliberately loose per-trial envelopes; no enumeration of all field elements, factoring oracle, unit-cost unbounded arithmetic, or storage of all trials is used in production. The fixture-assisted test search is not confused with the production algorithm.

## Literature and formal-status limits

The focused positioning is appropriately cautious. [Magma's primary documentation](https://docs.magma-maths.org/Modules/MultilinearAlgebra/Linear-invariants-of-tensors.html) explicitly covers self-adjoint spaces, centroids, and rewriting over an underlying field, and attributes its cyclic-algebra test to Brooksbank–Wilson. [The author's institutional record](https://digitalcommons.bucknell.edu/fac_journ/1203/) supports the cited cyclic-ring module-isomorphism scope. The [FGS author manuscript](https://www.di.ens.fr/~fouque/pub/eurocrypt05.pdf) supports the perturbation-kernel precedent. Search extraction from the [DGS author manuscript](https://www.di.ens.fr/~stern/data/St118.pdf), Theorem 1, confirms the random-instance and large-proportion quantifiers; direct PDF opening timed out during this review. This check supports the stated distinction, not a global absence-of-prior-art conclusion.

The partial Lean disclosure is accurate in the abstract and formal-status section. The two current modules establish an abstract algebraic image lemma and its disjoint-dual bridge. They do not establish the binary concrete representation, field recognition, sampler, constructor, certificate equivalence, or cost theorem. The header comment in `CorruptedFieldRecovery/Defect.lean` still calls the joint-surjectivity derivation unformalized even though `Independent.lean` supplies it; a low-priority comment correction would align the source with the coverage inventory.

## Feedback for the post-DOI Lean completion plan

Plan dependency-ordered milestones with checkable statement/axiom evidence, without changing the already valid partial-coverage label:

1. Concrete binary alternating tensors, finite coefficient encoding, common support, and full-mode-image/nonzero-compatible facts.
2. Four-contraction radical/adjoint theorem and explicit trace/coordinate transport from F2[T] to reconstructed determinant coordinates. Do not replace the actual field-identification claim by assuming its conclusion.
3. Finite-field cardinalities, proper-subfield generator bound, conditional sampling in the annihilator, translate union bound, and exact rational beta/gamma estimates.
4. A finite, bounded mathematical constructor and tape semantics, deterministic verifier soundness on all inputs, good-trial completeness, trial/random-bit caps, and amplification. Adaptive early stopping requires a bounded-tape argument or an explicit coupling to independent full tapes.
5. A specified bit-operation/storage model and all stage costs, including validation, failed trials, counter, field arithmetic, and serialized output; then assemble the exact manuscript theorem and audit its hypotheses and transitive axioms.

These are separate from a source-refinement proof for Python, which is unclaimed. Preprint release should precede this work under the current instruction. A later formalization result can be a separately identified revision, preserving the DOI record and accurately identifying which archived version carries which evidence.

## Follow-up primary-source checks requested by the coordinating reviewer

The indexed publisher metadata independently confirms Jan Hora, *Autotopisms and Isotopisms of Trilinear Alternating Forms*, Communications in Algebra **40**(4) (2012), 1438–1455, DOI `10.1080/00927872.2011.551899`, published online 5 April 2012. A subsequent direct publisher-page open returned HTTP 403; publisher search extraction remained available. Hora 2019, p.628, identifies its ring construction as a generalization of trace-derived forms introduced in reference [8]; p.636 identifies [8] as the 2012 paper. A narrow supported manuscript sentence is: “Hora describes his ring forms as a generalization of trace-derived forms introduced in his earlier work.” Cite both papers. This does not imply that the 2012 paper's full results were screened for subsumption.

For release metadata only, an anonymous read-only HTTP GET to [Zenodo's current license vocabulary entry](https://zenodo.org/api/vocabularies/licenses/other-open) returned HTTP 200 and JSON containing `id: other-open`, `title.en: Other (Open)`, `type: licenses`, and `revision_id: 1`. The legacy `/api/licenses/other-open` endpoint returned HTTP 404. The current vocabulary therefore contains the intended generic open-license identifier. The [official developer documentation](https://developers.zenodo.org/) describes `.zenodo.json` as following deposit metadata and explains that a selected license applies across the deposition's files. For the combined manuscript/software archive, the generic `other-open` classification should be accompanied by a clear component mapping: manuscript text/PDF CC-BY-4.0; code/Lean Apache-2.0. Choosing either specific license as though it covered every component would misdescribe this package. These checks used no credentials and performed no deposit, release, or metadata mutation; actual post-archive metadata still requires verification.

## Delta review of the prepared preprint changes

Reviewed the working-tree delta against the baseline on 28 October 2026. The reviewed `manuscript/main.tex` SHA-256 is `a24c45d2d587060a780e6817c222d572e0fc292b81a4d4ceed69d5918f1b9b47`. Files examined for this follow-up: `manuscript/main.tex`, `README.md`, `manuscript/README.md`, `CITATION.cff`, `.zenodo.json`, `CorruptedFieldRecovery/Defect.lean`, `docs/lean-verification.md`, `formal/coverage.json`, `tools/check_release_readiness.py`, `tools/check_lean.py`, and `PROVENANCE.md`. The consolidated disposition file referenced in README did not yet exist at inspection; its final creation and evidence receipts remain the coordinating reviewer's task.

F1 is resolved for the present preprint: the manuscript and supporting documentation expressly permit publication before full formalization, retain partial-coverage disclosures, and the default readiness path no longer requires complete Lean coverage. Strict mode continues to fail for the actual incomplete inventory. F2 is resolved: the inserted scalar-field isomorphism, coordinate relation `f(x)=B sigma(g(x))`, and `c'=sigma^{-1}(c det B)` trace identity correctly transport the planted component into the reconstructed coefficient space. F3 is resolved by the explicit third-mode warning and more precise dual-injectivity wording. F4 is resolved by the narrow historical sentence and accurate 2012 bibliography entry. The outdated Lean header comment is corrected without inflating its formal scope. The immutable-integer construction correction from the other review preserves the conservative headline bounds.

The citation record labels software Apache-2.0 and explicitly distinguishes the manuscript license in its notes. `.zenodo.json` uses the verified `other-open` package classification, clearly maps text/PDF to CC-BY-4.0 and code/Lean to Apache-2.0, labels the work a preprint, and makes no complete-formal-verification or human-peer-review claim. These metadata are consistent with the intended combined archive; actual deposited metadata is still to be checked after archival.

One nonblocking future-tool limitation remains: strict mode derives its required set from the inventory rather than enforcing the fixed complete-manuscript obligation IDs. Deleting `main_theorem` or another required obligation, or changing its `required` field to false, could evade that future completion check. Before claiming complete Lean certification, require the full expected ID set with required status and an audited final-theorem export, then manually inspect the exact theorem statement/hypotheses. Current inventory remains false/incomplete, so this limitation does not undermine the present preprint's disclosure or require delaying its release. The script is an evidence-consistency check, not an independent mathematical determination that the statements listed in its inventory cover the entire paper.

Scoped outcome: no unresolved mathematical, attribution, license-description, or partial-formalization publication blocker was found in this delta. This follow-up did not rerun tests, Lean builds, PDF rendering, or release operations. It does not certify the final regenerated PDF, evidence receipts, consolidated dispositions, repository release, or Zenodo archive, which are being handled separately.

Remaining to-do list: finish consolidated dispositions and fresh package/PDF evidence; publish and verify the actual first archive/DOI; evaluate and execute the post-publication Lean plan, including strict-gate coverage completeness before any full-certification claim.
