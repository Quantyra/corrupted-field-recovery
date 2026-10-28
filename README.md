# Certified recovery of trace-determinant structure under low-dimensional corruption

**Preprint v0.1.0 and reproducibility package. Lean verification is partial: the complete recovery theorem and Python implementation are not formally certified.**

Published version DOI: [10.5281/zenodo.23744566](https://doi.org/10.5281/zenodo.23744566). [Download the PDF](https://github.com/Quantyra/corrupted-field-recovery/releases/download/v0.1.0/main.pdf). Concept DOI for all versions: [10.5281/zenodo.23744565](https://doi.org/10.5281/zenodo.23744565).

The [preprint](manuscript/main.pdf) gives the standalone cubic-tensor theorem and proof, the exact compatible-representation certificate, conditional sampling estimates, and charged bit costs. [Editable source and build instructions](manuscript/README.md) are included. Here “certified recovery” means that every returned representation passes an exact certificate checker; it does not mean complete Lean certification.

The input is a dense binary alternating trilinear tensor on dimension `n=3s`. Its promised structure is a nonzero trace-determinant over an unknown field plus a perturbation supported on at most `R` unknown covectors. For `s>=2R+5`, the bounded reader uses at most `8*2^(4R)*h` trials and `(4n+s)` fair bits per trial. It returns a fully checked compatible representation or explicit failure. It does not promise unique recovery of the planted field.

## Run the implementation and checks

The implementation has no third-party Python dependencies. Python 3.13.7 was used for the saved receipt.

```text
python tests/check_recovery.py
```

[The receipt](artifacts/recovery-checks.json) pins the tested source bytes and distinguishes ordinary seeded recovery from fixture-assisted lemma tapes. It records 200 exact probability-bound checks, nine field identifications, 104 two-translate checks, independent pointwise certificate checks, altered-input/certificate controls, malformed-input rejection and an exact bounded-failure tape. Finite tests do not prove the theorem or certify the Python program in Lean.

Production API: `recover(n, coefficients, rank_limit, h, rng)` in [src/recovery.py](src/recovery.py). Coefficients are the `binomial(n,3)` bits indexed by increasing triples in lexicographic order. A valid RNG provides `getrandbits(k)`; the theorem assumes independent fair bits, whereas seeded PRNGs are reproducibility devices. The independent serialized-certificate checker is `verify(n, coefficients, rank_limit, certificate)`.

[Development failures](artifacts/development-failures.json) retain an outside-promise small-field refusal. It can be replayed with `python tests/replay_small_field_failure.py`; this optional run executes all 32,768 trials. Failure is not evidence that no other representation exists.

## Lean certification

Lean is pinned to 4.30.0 and mathlib to `c5ea00351c28e24afc9f0f84379aa41082b1188f`; dependency revisions are in `lake-manifest.json`.

```text
lake update
lake exe cache get Mathlib.LinearAlgebra.Dual.Lemmas Mathlib.LinearAlgebra.Prod Mathlib.Tactic.Abel
python tools/check_lean.py
python tools/check_release_readiness.py
python tools/check_release_readiness.py --require-complete-lean
```

The present Lean library proves the algebraic defect-image lemma and derives joint surjectivity from disjoint original/translated dual spaces. It is not the complete manuscript theorem. [The formal coverage inventory](formal/coverage.json) records the remaining input-model, field-identification, probability, constructor, certificate, and cost obligations. Python source verification is a separate unclaimed extension, not an extra prerequisite for manuscript certification. The default readiness command checks this preprint's package evidence and reports the partial formalization status. The stricter `--require-complete-lean` command intentionally fails until complete manuscript certification is established; a successful library build alone cannot satisfy it.

## Evidence and scope

- [Provenance and authorship](PROVENANCE.md) preserve the historical R05-08 revision and paths.
- [Focused primary-source comparison](docs/prior-art.md) attributes determinant forms, adjoint/centroid machinery and perturbation-cancelling directions. Global priority is unestablished.
- [PDF diagnostics and visual inspection](artifacts/pdf-checks.json) identify the inspected bytes and every reviewed page.
- [Three-model review and dispositions](docs/reviews/2026-10-28-disposition.md) distinguish reviewer judgments and exploratory checks from saved reproducible test artifacts. These are AI-assisted internal reviews, not human peer review.
- Software and Lean: [Apache-2.0](LICENSE). Manuscript: [CC-BY-4.0](LICENSES/CC-BY-4.0.txt). [Citation metadata](CITATION.cff) identify version 0.1.0. Zenodo metadata uses “Other (Open)” for this mixed-license package and states the per-component licenses.

The cubic-only bound does not replace the separate `s>=7R+5` condition for the broader phase-recovery application. No complete circuit simulation, quantum advantage, external counting-backend implementation, BPP/BQP result, or independent peer review is claimed.

## Post-publication cross-provider review

The original three reviews were all OpenAI models. Following the request for Grok, Agy and Claude, all three additional reviews are complete: Claude (returned `claude-opus-5-5`), Agy (configured Gemini 3.8 Flash High), and Grok (returned `grok-4.7-build`). They examined the published source and proposed Lean plan; Grok also inspected current working corrections. The plan contained a summary of prior reviews, so these passes are not fully blind. See the [follow-up dispositions](docs/reviews/2026-10-28-cross-provider-disposition.md).

Working-branch corrections include accepting the degree-one field polynomial `p=X`, explicit [resource-model clarification](docs/resource-model-clarification.md), and a required `two_translate_bridge` obligation distinct from the proved abstract kernel. The full recovery suite and [focused review edge cases](artifacts/review-edge-cases.json) pass. These changes and additional reviews are post-publication material; they are not present in the immutable v0.1.0 archive. The archived manuscript remains explicitly only partially Lean verified.

## Release status

Version 0.1.0 was [published on 28 October 2026](https://github.com/Quantyra/corrupted-field-recovery/releases/tag/v0.1.0), at commit `1de9785ec38d6fa4064b0279e2a444e47a2f2413`. The [Zenodo record](https://zenodo.org/records/23744566) is published as a preprint. All 44 archived files match the Git tag byte for byte, and the GitHub PDF asset matches the archived manuscript. Metadata, both DOI resolutions, and checksums are verified in [release state](artifacts/release-state.json) and [archive evidence](artifacts/zenodo-archive.json). Reproduce the archive comparison with `python tools/verify_archive.py 23744566 v0.1.0`.

The tag preserves the reviewed partial-formalization snapshot. DOI citation links and post-publication verification receipts were added to the main branch after archival; they are not retroactively claimed to be in that snapshot.

Remaining to-do list: evaluate and complete the planned Lean certification of the manuscript theorem.
