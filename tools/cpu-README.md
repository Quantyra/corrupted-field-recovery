# Prospective CPU captures

Dan's 2026-11-07 PaperMill direction selects tt-quietbox for proof work and CPU-01/CPU-02 for compilation. Historical GCP receipts keep their original host identity. This controller now supports **local capture preparation only** for the prospective CPU route:

```text
python tools/gcp_cfr.py capture --compile-host cpu-02 --label current-coefficient-fit --target CorruptedFieldRecovery.RawCoefficientFitScalarResidue --audit-export CorruptedFieldRecovery.rawCoefficientFitAugmentedArrayRun_refines --audit-export CorruptedFieldRecovery.rawCoefficientFitModelScalarResidue_eq_rawCandidateScalar --audit-export CorruptedFieldRecovery.rawCoefficientFitScalarResidue_eq_powerCoordinates
```

Packets go to `evidence/cpu/<run>/`. They freeze exact offered working-tree bytes (including untracked owned Lean sources), dependency pins, generated type/axiom audit and the loaded capture controller. CPU packets require explicit targets and audited exports, reject `--no-audit`, and label host `CPU`, specific prospective instance, `NOT_ESTABLISHED` admission and `NOT_SUBMITTED` execution. They have no GCP project, zone or builder identity. A capture is not a compiled result, lease, receipt acceptance or permission to publish its source archive.

There is no CPU submit/runner implementation in this change. Do not send CPU packets through the GCP runner or rewrite cloud fields to bypass its guard. A prospective adapter must retain source/dependency checks before and after execution, pinned Lean commit, bounded stage timeouts, task-owned locking/custody, resource admission, warning baseline, emitted types and allowed-axiom audit, closed-log hashes and terminal failures. Never compile Lean/Lake/LSP on Windows. CPU host admission and the exact-source compiler role must be established before execution; no provisioning, cleanup, workload preemption or spending authority is granted here.

The November 2 six-error diagnostic applies to an older captured `RawCoefficientFitFlattening.lean`. Current offered bytes already add explicit `d` arguments and a revised refinement proof. Recompile the exact current dependency chain first; do not repeat a proof-generation request for an error not demonstrated against those bytes. Simple delimiter balance is operational inspection, not Lean parsing or acceptance.

Checks: `python tools/check_cpu_capture.py` exercises exact archive custody, CPU identity/admission separation, invalid-offer rejection and legacy GCP behavior without invoking Lean, SSH or cloud operations. Existing `tools/check_gcp_transport.py` retains the non-compiling GCP guard regression.

Remaining: implement/review a CPU adapter preserving the listed controls; obtain an admitted host/custody; compile the captured target/audit; inspect actual emitted diagnostics/types/axioms and manuscript scope. Planning remains PaperMill P002/S003/S012.
