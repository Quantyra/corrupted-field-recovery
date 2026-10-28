# Manuscript build

`main.tex` is the self-contained working manuscript, with its bibliography in the editable source. `main.pdf` is a draft, not a released or fully Lean-certified paper.

Build using Tectonic 0.17.0:

```text
tectonic --keep-logs manuscript/main.tex
```

Read the source, PDF and validation receipts together. Publication remains dependent on complete Lean certification and final consistency validation. The cubic-only bound is not transferred to the broader quantum application.

Text and PDF are licensed under CC-BY-4.0; see `../LICENSES/CC-BY-4.0.txt`. Authorship, assistance and source lineage appear in `../PROVENANCE.md` and in the paper.
