# CFR cloud verification controller

`gcp_cfr.py` prepares immutable source captures and controls the dedicated
`quantyra-cfr-lean-builder-20261028a` builder in project `quantyra-lean-cert-20260915`,
zone `us-central1-a`, using the authenticated `dfredriksen@quantyra.org`
account. It does not import or overwrite historical Space controller state.
The active identity/toolchain/cache namespace is pinned in
`tools/gcp-builder-profile.json`. Captures from a different builder are rejected;
the shared builder's prelaunch failures remain immutable historical evidence.
No Lean command runs on the workstation. `gcp_cfr_runner.py` executes only
on Linux with an explicit cloud run identity.

Invoke with an available Python interpreter; the controller uses the installed
Cloud SDK's bundled Python for gcloud operations:

```text
python tools/gcp_cfr.py preflight
python tools/gcp_cfr.py capture --commit COMMIT --label baseline
python tools/gcp_cfr.py capture --label development --target CorruptedFieldRecovery.MODULE --no-audit
python tools/gcp_cfr.py capture --label audit --target CorruptedFieldRecovery.MODULE --audit-export CorruptedFieldRecovery.DECLARATION
python tools/gcp_cfr.py submit --run RUN
python tools/gcp_cfr.py resume-prelaunch --run RUN
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
`resume-prelaunch` continues a preserved upload failure only before any launch
intent or runner exists. It rechecks ownership/process guards, uploads to the
observed absolute remote home (PuTTY SCP does not reliably expand `~`), and
verifies transferred input/controller/archive hashes before the single launch.
Failed transport logs keep unique labels. A post-launch transport failure must
use `observe`, never this prelaunch continuation.

Repeated `--audit-export` options generate a capture-only audit containing
explicit types and transitive axioms for those declarations. Exact emitted
type blocks and raw logs are hashed for later semantic inspection; printing
and hashing a statement do not constitute acceptance of its manuscript scope.

Each submission has a unique immutable run directory and a single launch-intent
record. An SSH/observation timeout requires observation of the same run; the
controller refuses a duplicate launch. Stage stdout/stderr, outcome, command,
timing, exact input/dependency identities, and terminal/axiom receipts remain
under `evidence/gcp/RUN`. A failed stage remains a failed result; absence of a
terminal receipt is not success. Failed authentication cannot establish VM
state or authorize a claim that a compiler ran.

The remote task owns `~/quantyra-cfr-runs/cfr-lean430-c5ea-isolated-20261028a` as a
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

A separately recorded task reacquisition may authorize shutdown through
`stop-owned --run RUN --ownership-receipt RECEIPT/ownership.json`, relative to
`evidence/gcp`. The controller validates its successful exact VM-start command
and retains the original ownership observation unchanged. Collection, process,
lock and unrelated-workload guards still apply.

Remaining to-do list: preserve the baseline cloud outcome and continue exact-byte
proof captures, compilation and audits.

## Dedicated builder lifetime and network

Dan explicitly requested the isolated profile after another workflow stopped the
shared machine during upload. It has the same e2-highmem-8 capacity, a fresh
100GB balanced boot disk and pinned Ubuntu24.04 image; no shared disk/cache is
attached. GCE stops each start after four hours. No idle timer is installed,
because transfers and pending handles must remain safe. Explicit shutdown still
follows outcome preservation and workload checks.

The subnet has no Cloud NAT. A task-only ephemeral external IPv4 permits package,
Lean and mathlib cache downloads. Effective ingress remains existing IAP TCP22
and internal subnet traffic; no firewall/network policy was changed. The host
key is explicitly pinned. `stop-owned` removes this access configuration after
preservation, before stopping the dedicated VM. The creation ownership receipt
is a separate valid shutdown authority and never rewrites initial run state.
