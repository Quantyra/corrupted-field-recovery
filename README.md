# Certified recovery of trace-determinant structure under low-dimensional corruption

**Working manuscript and reproducibility package. Complete Lean certification and the first release remain unfinished. No DOI has been assigned.**

The [seven-page draft](manuscript/main.pdf) gives the standalone cubic-tensor theorem and proof, the exact compatible-representation certificate, conditional sampling estimates, and charged bit costs. [Editable source and build instructions](manuscript/README.md) are included.

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
```

The present Lean library proves the algebraic defect-image lemma and derives joint surjectivity from disjoint original/translated dual spaces. It is not the complete manuscript theorem. [The formal coverage inventory](formal/coverage.json) records the remaining input-model, field-identification, probability, constructor, certificate, and cost obligations. Python source verification is a separate unclaimed extension, not an extra prerequisite for manuscript certification. The readiness command intentionally fails until complete manuscript certification and all package checks are recorded. A successful library build alone cannot satisfy that gate.

## Evidence and scope

- [Provenance and authorship](PROVENANCE.md) preserve the historical R05-08 revision and paths.
- [Focused primary-source comparison](docs/prior-art.md) attributes determinant forms, adjoint/centroid machinery and perturbation-cancelling directions. Global priority is unestablished.
- [PDF diagnostics and visual inspection](artifacts/pdf-checks.json) identify the inspected bytes and every reviewed page.
- Software and Lean: [Apache-2.0](LICENSE). Manuscript: [CC-BY-4.0](LICENSES/CC-BY-4.0.txt). [Citation metadata](CITATION.cff) identify an unreleased development version without inventing a DOI.

The cubic-only bound does not replace the separate `s>=7R+5` condition for the broader phase-recovery application. No complete circuit simulation, quantum advantage, external counting-backend implementation, BPP/BQP result, or independent peer review is claimed.

## Release status

On 28 October 2026 the repository had no GitHub releases and an active Zenodo release-event hook. Publication is already authorized. Complete Lean certification and final readiness remain required before the first versioned release; afterward the actual archive, metadata and version/concept DOIs must be verified.

Remaining to-do list: complete Lean certification of the manuscript theorem; finish the final consistency audit; publish and verify the first GitHub release and Zenodo archive.
