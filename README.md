# Certified recovery of trace-determinant structure under low-dimensional corruption

A standalone manuscript and reproducibility companion from Quantyra.

**Status: manuscript in preparation.** This repository has been created for the paper. The manuscript, standalone implementation, and release artifacts are not yet included. No paper release or DOI has been issued.

## Scope

The proposed result concerns an explicitly represented alternating trilinear tensor over a binary vector space. Its promised structure is a trace of a determinant over an unknown finite extension field, plus a perturbation factoring through an unknown small-dimensional covector space.

The paper will give a bounded randomized reconstruction algorithm, an exact certificate verifier, and explicit success-probability, randomness, bit-time, and storage bounds. The perturbation model is algebraic; it is not a statistical measurement-noise model.

## Relationship to existing work

Trace-determinant forms, tensor centroids, and recovery of algebraic structure through directions that cancel a perturbation have established precedents. The manuscript will compare the precise guarantee with ring forms, computational tensor invariants, and differential cryptanalysis of internally perturbed multivariate systems. The focused prior-art screen has not established global priority.

The standalone cubic-tensor statement and the stronger hypotheses needed for the quantum-circuit application will be stated separately. No BPP/BQP resolution or quantum advantage follows from this restricted recovery result.

## Provenance and review status

The starting point is the Quantyra Quantum Complexity research program's R05-08 result, recorded on 28 October 2026 at source commit `d2ae8c6fc275423c2276ba82644b8993660ec684`. Its source proof is `proofs/s173-corrupted-field-contractions-and-cost-2026-10-28.md` in that research repository.

A subsequent AI-assisted internal audit identified a cubic-only specialization requiring two translated defect spaces, rather than the seven used in the broader phase-recovery argument. The standalone manuscript must include the full proof and cost accounting for that specialization. Internal mathematical review and finite checks do not constitute formal verification or independent peer review.

Extracted artifacts will retain their source provenance. The broader research repository and unrelated research history are not part of this publication package.

## Release preparation

- Self-contained theorem, proof, and focused prior-art comparison.
- Standalone implementation, exact certificate verification, reproducible checks, and negative controls.
- Typeset PDF, editable manuscript source, bibliography, licensing, and citation metadata.

## Zenodo

The repository is ready to be enabled in Zenodo's GitHub integration. The first release will be prepared after the manuscript package is complete and the integration is enabled. Zenodo archives new GitHub releases from enabled repositories; see its [repository integration instructions](https://help.zenodo.org/docs/github/enable-repository/).

Remaining to-do list: complete the manuscript and reproducibility package; verify the release contents; publish the first version after Zenodo integration is enabled.
