# Manuscript build

`main.tex` is the self-contained v0.1.0 preprint, with its bibliography in the editable source. `main.pdf` explicitly discloses partial Lean verification; the main theorem is not fully Lean-certified.

Build using Tectonic 0.17.0:

```text
tectonic --keep-logs manuscript/main.tex
```

Read the source, PDF and validation receipts together. The first preprint precedes complete Lean certification under the current publication instruction. Final package validation remains required. The cubic-only bound is not transferred to the broader quantum application.

Text and PDF are licensed under CC-BY-4.0; see `../LICENSES/CC-BY-4.0.txt`. Authorship, assistance and source lineage appear in `../PROVENANCE.md` and in the paper.
