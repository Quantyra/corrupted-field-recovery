# CFR cloud verification controller

`gcp_cfr.py` prepares immutable source captures and controls the existing
`quantyra-lean-builder-01` builder in project `quantyra-lean-cert-20260915`,
zone `us-central1-a`, using the authenticated `dfredriksen@quantyra.org`
account. It does not import or overwrite historical Space controller state.
No Lean command runs on the workstation. `gcp_cfr_runner.py` executes only
on Linux with an explicit cloud run identity.

Invoke with an available Python interpreter; the controller uses the installed
Cloud SDK's bundled Python for gcloud operations:

```text
python tools/gcp_cfr.py preflight
python tools/gcp_cfr.py capture --commit COMMIT --label baseline
python tools/gcp_cfr.py capture --label development --target CorruptedFieldRecovery.MODULE --no-audit
python tools/gcp_cfr.py submit --run RUN
python tools/gcp_cfr.py observe --run RUN
python tools/gcp_cfr.py collect --run RUN
python tools/gcp_cfr.py stop-owned --run TASK_STARTING_RUN
```

A working-tree capture includes all current proof modules and the exact root,
audit, toolchain and dependency configuration bytes. The manifest records every
hash, validates UTF-8 without BOM, and lists exact dependency revisions.
The committed baseline capture avoids racing proof authors' successor edits.
Authors should offer stable hashes and retain those bytes until capture is
acknowledged. Captured source bytes are never normalized or rewritten.

Each submission has a unique immutable run directory and a single launch-intent
record. An SSH/observation timeout requires observation of the same run; the
controller refuses a duplicate launch. Stage stdout/stderr, outcome, command,
timing, exact input/dependency identities, and terminal/axiom receipts remain
under `evidence/gcp/RUN`. A failed stage remains a failed result; absence of a
terminal receipt is not success. Failed authentication cannot establish VM
state or authorize a claim that a compiler ran.

The remote task owns `~/quantyra-cfr-runs/cfr-lean430-c5ea-20261028` as a
persistent disk cache. It uses private dependency copies from the established
Space pinned-source archive, verifies their Git revisions and clean tracked
sources, and reuses the existing Lean 4.30 Linux installation read-only.
Public mathlib cache artifacts are obtained for the actual imports; dependency
and CFR build outputs remain task-owned. The persistent workspace survives SSH
sessions without a RAM checkpoint restore. Later receipts identify the last
successful cache predecessor. Other campaigns' sources, caches and processes
are not changed.

One task-owned `flock` serializes all compiler stages. Each stage has a bounded
1800-second timeout, with timeout termination restricted to that stage's own
child process group. Raw runner and stage logs are preserved on failure.
Baseline warning headers are retained with exact source/dependency identities;
later runs reject newly introduced owned warning headers. A successful
development result certifies only its requested targets. A full manuscript
certification claim additionally requires the actual complete statements,
their hypotheses and complete source/dependency/axiom audit to be reviewed.

Shutdown is allowed only for a handle whose recorded initial VM state was
`TERMINATED` and which started the VM. Preserve every launched outcome first,
verify no other work has acquired the VM, verify no Lean/Lake process remains,
and retain the task cache. The stop command checks collected outcomes, active
Lean/Lake processes and the task lock, and records the preserved cache and
verified final `TERMINATED` state. Its operator must also assess any unrelated
active workload before invoking shutdown. No new VM, machine-size change,
shared-cache cleanup, or historical-evidence replacement is part of this tool.

Remaining to-do list: authenticate the established account, verify live VM
state, run and preserve the baseline, and continue exact-byte proof captures.
