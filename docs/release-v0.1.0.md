# Preprint v0.1.0

First release of **Certified recovery of trace-determinant structure under low-dimensional corruption**, Daniel Eric Fredriksen, Quantyra Inc.

The manuscript gives the standalone theorem and prose proofs, bounded exact recovery algorithm, compatible-representation certificate, conditional sampling estimates, charged time/space/randomness bounds, and focused prior-art comparison. The package includes the eight-page PDF and editable source, dependency-free Python implementation and tests, pinned Lean sources, source-bound validation receipts, provenance, and three AI-model review reports with feedback dispositions.

For s >= 2R+5, the algorithm uses at most 8*2^(4R)*h trials and (4n+s) fair bits per attempted trial, with success probability at least 1-2^(-h). Every accepted representation is exactly checked, including outside the sufficient promise. Unique identification of the planted representation is not claimed.

**Lean verification is partial.** Seven intermediate declarations establish the abstract defect-image argument and its disjoint-dual bridge. The main theorem, probabilities, complete constructor, certificate checker and resource bounds are not yet fully Lean-certified. Python is independently tested, not formally verified. GPT-6 Astra, GPT-6.1 Terra and GPT-6.1 Sol provided AI-assisted internal review; no independent human peer review is claimed.

Review feedback clarified field-coordinate transport, dual injectivity and displacement mode images, corrected Python exterior-column packing accounting to a conservative O(n^9) stage bound (within the unchanged soft-O(n^12) envelope), added Hora's earlier precursor, and strengthened saved evidence checks. The broader quantum application retains its separate field-size condition; no BPP/BQP or quantum-advantage conclusion is asserted.

Validation: the saved recovery suite passes; the partial Lean library and seven-declaration axiom audit pass with only standard Lean foundations; every PDF page is rendered and inspected; the preprint readiness gate checks matching evidence. The complete-Lean gate intentionally remains unsatisfied. See artifacts and review reports for exact scope and hashes.

Licenses: manuscript CC-BY-4.0; software and Lean Apache-2.0. Zenodo's package metadata uses Other (Open) and records these per-component licenses.

Published version DOI: [10.5281/zenodo.23744566](https://doi.org/10.5281/zenodo.23744566). Concept DOI: [10.5281/zenodo.23744565](https://doi.org/10.5281/zenodo.23744565). Release commit: `1de9785ec38d6fa4064b0279e2a444e47a2f2413`. All 44 files in Zenodo's archive were compared byte for byte with the tag, and the GitHub PDF asset matches the archived PDF. Both DOI links resolve to the published record. The metadata matches the released title, author, date, version, preprint type, description and mixed-license mapping.

This DOI paragraph and the archive verification receipts were added after publication. The immutable v0.1.0 snapshot retains its pre-publication citation text and truthful partial Lean status.
