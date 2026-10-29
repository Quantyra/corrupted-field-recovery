# CFR GCP campaign checkpoint

Updated 28 October 2026. The isolated GCP baseline has passed and been collected.
The first binary/bridge and four-contraction development builds failed and their
diagnostics are preserved. Historical local receipts remain supplementary. `formal/coverage.json` and the root/audit exports
have not been promoted for the new drafts.

The established account is listed as active, but its token refresh failed with
an explicit reauthentication requirement. The saved preflight is
`cfr-preflight-20261028T211425Z-84e8cf`. VM status was not observable and no
instance was started. The user has been asked to renew that account's login.

Prepared immutable captures:

| Capture | Intended scope | State |
|---|---|---|
| `cfr-baseline-20261028T211424Z-5ddb91` | Original root/audit at committed `880bdfaab9a2213a0b84691296bf0f4219f8539e` | Captured; baseline build/audit pending |
| `cfr-binarytensor-dev01-20261028T211904Z-17e0fe` | First binary-tensor draft | Captured; superseded before compilation |
| `cfr-bridge-dev01-20261028T211935Z-7b8ae8` | Bridge draft and then-current binary dependency | Captured; dependency differed from initial author offer; superseded before compilation |
| `cfr-binary-bridge-dev02-20261028T212009Z-3ce03e` | Matched stable binary/bridge draft tuple | Captured; a source-inspection argument-order typo was later repaired; never compiled |
| `cfr-binary-bridge-dev03-20261028T212244Z-2ab65e` | Matched successor tuple after that repair | Captured; absent focused import then repaired; never compiled |
| `cfr-bridge-dev04-20261028T212416Z-4fd5bc` | Increasing-pair slice draft | Captured; misplaced namespace terminator then repaired; never compiled |
| `cfr-binary-bridge-dev05-20261028T212913Z-8c22b0` | Import/namespace-corrected tuple and explicit declaration audit | Captured; next development build/audit pending |

Every capture preserves exact offered bytes, a SHA-256 archive digest, source
digests, UTF-8/no-BOM validation and the complete pinned dependency revisions.
Capture acknowledgments permit authors to edit successors; each compilation
will use its own immutable archive, never a live author worktree.

The current `BinaryTensor.lean` and `Bridge.lean` files are **uncompiled drafts**.
The latest tuple is binary source SHA-256
`6e2866a02c3b29a47e55c2cf78c662eba27e5e73cae3b7d996774d761bb95d62`
and bridge SHA-256
`6f55088813114f0062e2c7a57e176504c935c195616c477f64376235e2f92145`.
The bridge contains valid Lean Unicode; an early author message calling it
ASCII-only was inaccurate. Neither draft closes a manuscript coverage item.

A later read-only preflight, `cfr-preflight-20261028T213425Z-5d3fbe`, again
found the configured account but failed token refresh before observing VM
state. No VM or compiler was started. An independent uncompiled one-bit
arithmetic cost prototype was captured as
`cfr-bitcost-dev04-20261028T214143Z-44e4f0` (source SHA-256
`5174288a682f34dab8d313b44938ee582c9c9e799444d96664df8b5b39a60dbb`).
Its dev01-dev03 captures and source-level review notes are preserved: dev01 had a
false control-charge equality; later revisions clarify address charges,
ghost counters and the declared storage measure. No version has been compiled
or accepted. The prototype does not yet prove a bounded PC layout, actual
runtime peak memory, variable-size array costs or manuscript complexity.

A further preflight, `cfr-preflight-20261028T214354Z-6878f2`, again failed
token refresh before VM state could be observed. An independent uncompiled
four-contraction source draft was captured as
`cfr-fourcontractions-dev02-20261028T214827Z-4621fb`, source SHA-256
`b6b8331aebe70c788e72fbced5ee4f04b6c335c8e83aadf31e98f60e627a8de3`.
It attempts the trace-pairing and generator-to-scalar steps only. The prior
capture and the source review of its reversed equality are preserved. Neither
capture proves the four-contraction field-identification theorem or changes
formal coverage. Both await GCP compilation and diagnostics.

The non-Lean readiness command was rerun and its accurately false result now
appears in `artifacts/release-readiness.json`; it reports missing compiled
evidence bindings for the five development modules. The prior working-tree result is preserved under
`cfr-readiness-20261029T003509Z-1f450f` alongside the exact new output, command
and exit code. This working-tree change does not alter the separately verified
first archive or its DOI.

The isolated cloud controls and cache/ownership policy are documented in
`tools/gcp-README.md`. Python syntax and immutable archive-member/hash checks
were performed locally without invoking Lean. The remote runner is prepared
but not yet cloud-tested. Full type/axiom checks for the new declarations will
be captured at acceptance, in addition to focused development builds.

The latest capture contains `checks/CaptureAudit.lean` with explicit universe,
implicit-argument and fully qualified name printing, named type-block markers,
and fresh transitive-axiom commands. It does not alter the shared root audit.
The runner will bind emitted type blocks and raw audit log hashes in its
terminal receipt. Mathematical acceptance remains separate from those hashes.
Its warning classifier is covered by a saved pure-Python nine-case fixture
covering both Lake/Lean header orders and excluding dependency paths. The
runner also fingerprints the actual cloud Lean/Lake executables, checks the
pinned Lean commit and rejects uncaptured stale owned source files in the
persistent workspace. No stale source/cache is silently deleted.

Historical initial resume sequence (the baseline now has a partial prelaunch
submission; follow the newer checkpoint below before any action):

```text
python tools/gcp_cfr.py preflight
python tools/gcp_cfr.py submit --run cfr-baseline-20261028T211424Z-5ddb91
python tools/gcp_cfr.py observe --run cfr-baseline-20261028T211424Z-5ddb91
python tools/gcp_cfr.py collect --run cfr-baseline-20261028T211424Z-5ddb91
```

Inspect the preserved successful baseline before submitting the next capture:

```text
python tools/gcp_cfr.py submit --run cfr-binary-bridge-dev05-20261028T212913Z-8c22b0
```

An observation timeout retains the same run handle. Do not resubmit or restart
it. Stop the task-started VM after all launched outcomes are preserved and
other ownership has been excluded, including after failed proof attempts.

Remaining to-do list: renew GCP login; observe live VM ownership/state; run and
preserve the baseline; compile the matched draft tuple, route diagnostics and
capture repairs; continue the selected complete-manuscript milestones.

## Authenticated prelaunch checkpoint

Authentication recovered in `cfr-preflight-20261028T221635Z-5f6958`; account and
VM queries passed. Inspection `cfr-inspect-20261028T221730Z-0ce8d5` found no active
Lean/Lake, an existing toolchain and 24GB free disk. Baseline handle
`cfr-baseline-20261028T211424Z-5ddb91` created its isolated remote directory but
its first PuTTY SCP failed on the tilde destination. The corrected absolute
home is `/home/dfredriksen_quantyra_org`, preserved in
`cfr-transport-diagnosis-20261028T222138Z-f0ac59`. The controller now constructs
validated absolute destinations, preserves guarded prelaunch resumptions and
verifies uploaded hashes before the single launch. The saved pure-Python
`tools/check_gcp_transport.py` regression passes; no Lean runs in that check.

Two subsequent transport interruptions coincided with external VM stops.
`cfr-shutdown-audit-20261028T223101Z-58be86` records `compute.instances.stop`
from the expected account and a Windows Codex CLI user agent at 22:25:00Z and
22:29:15Z, invocation IDs `861ed3b224e64983904d3b227966e50b` and
`93668108171046a6bd95fd27110a7ae4`. This compiler issued neither stop. It started the existing VM once
between those stops, recorded separately in
`cfr-vm-reacquire-20261028T222603Z-6fa338`; the original RUNNING observation is
unchanged. Do not restart while the other workflow's lifecycle control is unresolved.
`cfr-final-vm-state-20261028T223246Z-62e976` confirms TERMINATED, with final
stop timestamp 22:31:27Z.

All five small baseline input/controller files uploaded successfully after the
path repair. Bootstrap transfer was interrupted near 6.3MB; partial task-owned
files remain preserved. **No launch request was created, no runner started and
no Lean compiler ran.** The exact baseline archive remains unchanged. Read
`prelaunch-transport-checkpoint.json` in the baseline directory. Once lifecycle
ownership is coordinated and VM state is observed, continue this same handle
with `resume-prelaunch`; do not repeat `submit`. After launch, only observe and
collect that handle. Dev05 binary/bridge and later independent candidates have
not been submitted.

Four-contraction development captures dev03 through dev06 preserve the first
concrete determinant/contraction radicals and axis-preservation draft, including
source-level rewrite repairs. The latest is
`cfr-fourcontractions-dev06-20261028T222223Z-cb0e20`, source SHA-256
`231dd34c64891c8c9ff4bdd5d31e00a9ec6cbb8059f0a37775878ec207e290f4`.
Six exported type/axiom audit commands are prepared. These uncompiled
intermediate sources do not prove the full field-identification theorem or
change formal coverage. Do not expand a dependent uncompiled stack before
GCP diagnostics.

Remaining to-do list: coordinate external VM lifecycle control; resume and
preserve the existing baseline; compile/audit the binary/bridge and independent
candidates; complete the actual manuscript obligations.

## Isolated builder and first compiler outcomes

Dan explicitly requested a dedicated builder to avoid shared lifecycle conflict.
`tools/gcp-builder-profile.json` pins `quantyra-cfr-lean-builder-20261028a`,
instance ID `3335066512373302615`, in the established project/zone. It has the
same e2-highmem-8 capacity, a fresh 100GB disk and pinned Ubuntu24.04 image.
No shared disk/cache was attached. Creation and ownership are saved in
`cfr-isolated-create-20261028T224800Z-c092b2`. GCE enforces a four-hour per-start
STOP limit; there is no idle timer. Existing effective rules allow IAP SSH and
internal subnet traffic. With no existing Cloud NAT, a dedicated ephemeral
external IPv4 was added for outbound downloads only; no shared policy changed.
Shutdown must remove it after preserving all outcomes.

Provisioning fetched official Lean4.30.0 and verified archive SHA-256
`4dad74141c2c119ca1aa626656be83b8e14238afba97271fd7bf1eb3f081b319`.
The host key is pinned; full bootstrap/capacity output is preserved. Fresh
captures replace cloud identity only; old shared prelaunch evidence is unchanged.

| Isolated handle | Outcome |
|---|---|
| `cfr-isolated-baseline-20261028T224830Z-75ad79` | Passed, collected and log hashes verified; root build/audit exit0, zero owned warnings, standard three axioms only |
| `cfr-isolated-binary-bridge-dev01-20261028T225253Z-c544e3` | Failed build, collected; first error missing Field(ZMod2) instance in BinaryTensor; Bridge/audit not reached |
| `cfr-isolated-binary-bridge-dev02-20261028T231148Z-14cf5a` | Failed build, collected; later repairs led to green binary/bridge evidence |
| `cfr-isolated-fourcontractions-dev01-20261028T225446Z-b42475` | Failed build, collected and routed for repair |
| `cfr-isolated-bitcost-dev01-20261028T225447Z-93b03f` | Captured; superseded before launch by the readable-audit cost attempt |

The baseline preserves exact old baseline source/dependency identities, verified
Lean commit `d024af099ca4bf2c86f649261ebf59565dc8c622`, seven audited declarations
and only `propext`, `Quot.sound`, `Classical.choice`. It does not certify any new
draft or the full manuscript. Development candidates reuse the task-owned cache;
failed attempts remain immutable evidence. Formal coverage remains unchanged.

Remaining to-do list: finish the compiler/repair/audit loop, preserve every
outcome, then remove task egress and stop the dedicated builder; complete all
remaining manuscript obligations.

## Current accepted intermediate scope

The six-field-lemma full-type gate is green at
`cfr-isolated-four-fulltype-recheck-20261028T235851Z-925763`; the binary/bridge
gate is green at `cfr-isolated-binary-bridge-dev06-20261028T235231Z-b47944`.
Both outcomes are collected, log hashes verified, warning-free against the
frozen baseline and restricted to the three reported standard axioms. Root
inspected the actual untruncated declaration text. Their conclusions are
intermediate: the dense codec, complete two-translate application, complete
field identification, sampling, constructor and charged costs remain open.

Preserve the gate history: `094ef6` rejected universe-qualified standard axiom
spellings; `2f5cf2` passed build/axioms but its axis type contained 21 truncation
glyphs, so full-type acceptance was withheld; `44587f` printed full readable
types but a notation-dependent token criterion failed. None of these receipts
was rewritten. `925763` has exactly the same readable audit stdout as Root's
manual review, with the corrected automated gate.

The active audit generator keeps all outer binder names/types, universes and
full names, raises pretty-printer limits, enables deep terms/proofs and rejects
empty or truncated type blocks. Axiom validation retains raw universe spellings
and accepts only the exact standard declarations. Fixtures reject project,
sorry/native, spoofed, malformed, duplicate and truncated profiles. Lexical
checks supplement the required semantic statement inspection.

The block-form repair `cfr-isolated-four-block-dev02-20261029T001053Z-6b82bf`
has passed with Root's narrow statement inspection. The common-block attempt
`cfr-isolated-four-common-dev01-20261029T002212Z-8c46c5` failed on one multiplication-order proof step; the exact correction is captured at `cfr-isolated-four-common-dev02-20261029T004012Z-300888`. Frozen
successors are dense-input `cfr-isolated-denseinput-dev02-20261029T002853Z-af3d02`
and bounded cost `cfr-isolated-bitcost-dev03-20261029T003340Z-d8f6de`.
Initial dense-input and cost failures are preserved. The older seven-source
queue finished before DenseInput activated the eighth owned source; no
uncaptured source or cache was silently deleted.

Remaining to-do list: preserve the queued development outcomes and repairs;
complete the actual input/field/algorithm/probability/cost obligations; remove
task egress and stop the dedicated VM after preserving the batch.

The isolated cost repair [`d8f6de`](cfr-isolated-bitcost-dev03-20261029T003340Z-d8f6de/collected/terminal-receipt.json) completed build and readable type/axiom audit at 2026-10-29 00:53:00 UTC: seven declarations, zero warnings, and only the standard approved axioms (the full-adder theorem is closed). Its [raw audit](cfr-isolated-bitcost-dev03-20261029T003340Z-d8f6de/collected/logs/audit.stdout.txt) is preserved with verified log hashes. This checks one-bit modeled transition accounting and separate ripple arithmetic; the declared 40-bit measure does not establish actual peak storage or PC layout adequacy. M0 remains open.

DenseInput repair [`af3d02`](cfr-isolated-denseinput-dev02-20261029T002853Z-af3d02/collected/terminal-receipt.json) failed build: unknown `Pi.proj`, redundant tactics after closed goals, and characteristic-two residual cancellations. The complete failed logs remain preserved. Successor `32b15c` captures the offered repair; no codec roundtrip or M1 acceptance is inferred. Four-contraction standard-coordinate drafts `830be3` and successor `4640e5` are immutable uncompiled captures; the former has a recorded forward-reference rejection. The common-block repair `300888` retains its separate queued identity.

Cost prelaunch evidence preserves a Windows gcloud crash after the remote directory guard and a subsequent upload failure caused by missing local `run.sh`. Controller preparation now occurs before the remote guard and reconstructs missing execution metadata from the retained runner for prelaunch continuation. Pure-Python regression verifies exact script hashes and absence of launch side effects. The same cost handle was resumed, verified, and launched once; neither failed prelaunch operation launched a compiler.

Common-block repair `300888` emitted a green terminal receipt at 2026-10-29 00:56:00 UTC: ten readable declarations and zero warnings, including actual off-diagonal pairing relations and the common self-adjoint helper. The observe transport crashed only after delivering the full receipt; no compiler was rerun. Root semantic review and complete collection are tracked separately. This remains an intermediate field-model result; standard-coordinate identification and basis transport are not inferred from it.

DenseInput `32b15c` failed on one remaining scalar-linearity multiplication identity; its complete raw logs are collected and hash verified. Successor `ef1a25` captures only that repair. Standard-coordinate four-contraction draft `4640e5` failed on three recursive simplification calls and four redundant tactics, with two linter warnings; its complete logs are also collected. These failed captures establish no decoder roundtrip or standard-coordinate theorem acceptance. Prior narrow green intermediate results and their raw audits remain preserved independently.

Standard-coordinate four-contraction repair [`9eadca`](cfr-isolated-four-standard-dev03-20261029T010850Z-9eadca/collected/terminal-receipt.json) passed build and full readable audit at 2026-10-29 01:16:29 UTC, with 36 declarations and zero warnings. Root inspected the [actual emitted types](cfr-isolated-four-standard-dev03-20261029T010850Z-9eadca/collected/logs/audit.stdout.txt): for finite K with prime-field algebra, nonzero c and at least one generating a/b/d, the concrete standard four balances are equivalent to a scalar map. The fourth coefficients remain inside trace. Arbitrary sampled-basis transport and dimension are separate obligations. Transport draft `8ebf1c` is preserved as superseded before compilation; corrected reverse implication is captured in `b40ae8`.

DenseInput infrastructure [`9cd41b`](cfr-isolated-denseinput-dev05-20261029T011305Z-9cd41b/collected/terminal-receipt.json) passed build/full readable audit at 01:21:55 UTC, with 15 declarations and zero warnings; [raw audit](cfr-isolated-denseinput-dev05-20261029T011305Z-9cd41b/collected/logs/audit.stdout.txt) and all log hashes are retained. This validates the payload/selectors, computable coordinate vector/encoder definitions, minor alternation and semantic coefficient agreement. Both codec roundtrips remain separate draft work (`0249dd` static-review failure, corrected capture `048321`). No complete M1 or manuscript coverage is promoted.

The dense finite-function codec [`42ba02`](cfr-isolated-denseinput-roundtrip-dev04-20261029T013625Z-42ba02/collected/terminal-receipt.json) passed build/readable type/axiom audit at 2026-10-29 01:46:52 UTC, with 21 declarations, zero warnings and only approved standard axioms. Root inspected the [actual complete types](cfr-isolated-denseinput-roundtrip-dev04-20261029T013625Z-42ba02/collected/logs/audit.stdout.txt) and source: minor basis evaluation assumes both triples strictly increasing; decoder alternation holds for any payload; encode-after-decode is unconditional; decode-after-encode requires exactly `IsAlternating C`. The computational encoder/decoder use `Pi.single` and finite sums. Physical lex-byte serialization, costs, field/support promise and verifier remain open. Predecessor `048321`/`53b992` failures and the same-handle Windows transport failure/resumption remain intact.

The latest four-contraction source `57592dc8a091b056bfaa38b848d53bc7be4f748d019ec5eab99ed1f14222c604` is captured as `d9123c` with 66 audited declarations prepared, but has not been compiled. It includes pending sampled-basis determinant/balance/dimension additions and exact predecessor diagnostic repairs. Neither the failed dimension `79b561` nor the green standard-coordinate `9eadca` validates those new bytes. The next bounded builder start must compile this exact immutable capture and preserve full diagnostics/audit before any acceptance.

Read-only readiness was refreshed in [`1670c2`](cfr-readiness-20261029T015239Z-1670c2/receipt.json), preserving the prior artifact: exit 1, `ready=false`, `complete_lean=false`, with five missing source/evidence bindings in the release inventory. This does not erase the independent saved green GCP receipts above, and those partial receipts do not close the full formal obligations. The coverage inventory is unchanged.

The dedicated builder is safely stopped: [`49450d` shutdown result](cfr-isolated-denseinput-roundtrip-dev04-20261029T013625Z-42ba02/cfr-shutdown-20261029T015003Z-49450d-result.json). All launched outcomes were collected, no Lean/Lake process or task lock remained, and persistent cache/output hashes were preserved. Its numeric instance ID matched the original creation receipt; task-only external egress was removed and final state verified `TERMINATED`. No live compiler/SSH handle remains. Resume the active goal through the [bounded continuation runbook](../../tools/gcp-README.md#bounded-continuation-on-the-dedicated-builder): inspect/start this dedicated VM once, preserve the fresh four-hour STOP ceiling, restore only task-owned egress if needed, then compile the unlaunched `d9123c` source capture with its full fresh audit. Earlier failed and superseded captures are historical, not duplicate launch instructions.

The active goal resumed the same dedicated builder through [`abac32`](cfr-isolated-restart-20261029T020104Z-abac32/ownership.json). Read-only inspection confirmed original instance ID `3335066512373302615`, `TERMINATED`, no external access config, and effective ingress limited to IAP TCP22 plus the internal subnet. One successful start and one task-only ephemeral egress restoration were preserved separately; the actual fresh STOP ceiling is 2026-10-29 06:02:12.544296 UTC. Persistent disk/cache and pinned host key were retained; shared networking/builder were not changed.

Sampled-identification `d9123c` failed build on pinned basis/RestrictScalars APIs and prime-field typeclass elaboration. Its successor `0b2ea0` removed the initial Basis cascade but failed determinant/binder, scalar-action namespace and final characteristic-two cardinality proofs. Both exact terminal logs are collected/hash verified, including the failed Windows transport package receipt. Neither run reached a passing type/axiom audit.

New ninth owned source `Support.lean` was captured as `2fd6dc` before author edits; Root's static Subspace/swap review is saved. Corrected successor `838358` was compiled only after the last eight-source run was collected, activating the nine-source inventory without deleting cached sources. It failed quotient/coannihilator/lift API elaboration; complete raw logs were collected and routed to its author. Old eight-source drafts are historical and must not be replayed after this activation. New captures include all nine owned source files, with acceptance restricted to requested targets and actual emitted declarations.

The controller now preserves `loaded-controller.py` bytes matching each execution manifest's controller hash, including exact retained copies for `d9123c`/`0b2ea0`; it refuses replacement. Console summaries handle instance lists without dumping startup metadata, while raw receipts remain exact. Shutdown additionally verifies the numeric ID in fresh-start ownership receipts. Pure-Python execution-hash/transport regression passes; no Lean/Lake was executed locally.


The replacement sole compiler recovered the already launched sampled-identification
`0b3c0f` through same-handle observation and collection; no compiler was relaunched.
Its build failed at 02:59:55 UTC on two determinant-transport proof details
(let-bound standard basis and a coerced coordinate-map rewrite). Full stdout,
stderr and terminal hashes are retained. Exact repair SHA-256
`5f6019c5bd872045ecf13c9d746763cd8da89b7fb0cae71d6fcd24fdabd62ff5`
is captured as `11c3b5`, with the same 66-export audit policy, pending compilation.

Support `cccbb2` launched once as PID 8102 and failed at 03:09:31 UTC.
Its originating failure is the 200000-heartbeat `whnf` timeout at line 77;
unknown `supportedQuotientLift` references and two unused-simp warnings are
consequences in that failed build. The complete raw logs were collected and
independently rehashed against every terminal log digest before routing the
actual originating diagnostic to the author. No audit or formal coverage was
promoted. The non-compiling transport regression passed. Fresh submission
inspection confirmed instance `3335066512373302615`, a four-hour STOP duration,
and the same start; the earlier conservative ceiling remains
2026-10-29 06:02:12 UTC.

Remaining to-do list: compile and collect `11c3b5`; capture and compile the
Support repair; inspect exact green types/axioms; continue the manuscript
milestones; safely stop the dedicated builder after preservation and workload checks.


Sampled-identification `11c3b5` subsequently failed at 03:14:31 UTC on
one no-progress `simp` call and one unnecessary-`simpa` warning; its complete
raw logs are collected. The author's statement-preserving repair SHA-256
`254ee5392d54ee0247fb4cb0f7a67b7835db5521ea51d83a81866d234a6d8f32`
is captured as `2bfb9f` with the same 66-export audit. Support successor
`80c78b91ac2748eddb83c02238a802e33cdb4e1d83cd0aebd6fc34f923aab6ec`
is captured as `b9a0d4`; it splits the timed-out declaration into smaller
proved lifts without changing the heartbeat limit or suppressing warnings.
Both archives and all captured member hashes were checked locally without Lean.

Remaining to-do list: preserve Support `b9a0d4` and Four `2bfb9f` outcomes;
inspect actual green statements/axioms; continue full certification; safely
stop the builder after collecting every launch and excluding other workloads.


Four `2bfb9f` failed at 03:26:59 UTC on the explicit remaining equality
between the determinants of permuted basis vectors; no warnings were emitted.
Its complete logs are collected. Support `b9a0d4` failed at 03:21:33 UTC on
the outer lift's 200000-heartbeat timeout and two no-op `change` warnings;
its complete logs are collected. Both collections preserve Windows-gcloud
crashes that occurred after delivering package hashes; same-handle read-only
collection retries succeeded without compiler reruns.

Four successor `1d211e` captures SHA-256
`d05c0fbe41a0125a1b4f3121317b481d1eb34bc547cedcf29b4a05251040aa04`
with the same 66-export audit. Support successor `57add0` captures SHA-256
`9c97eea57e6efa53f01ca45df8fb0669ceba93c3ad8d8c0adfb7f81be9297fc8`
with the same 11-export audit. The latter removes the no-op tactics and scopes
a 3200000-heartbeat allowance to the outer lift under Root's direction;
it does not change a theorem statement, stage timeout, live input or VM ceiling.
Support launched once as PID 11281 at 03:36:24 UTC and was still running build
at the 03:38:28 observation. A premature read-only collection was correctly
refused by the missing-exit-code guard and is retained as failed transport.

Remaining to-do list: retain terminal outcomes for Support `57add0`, then
Four `1d211e`; review actual green declarations/axioms; continue the complete
manuscript milestones; safely stop the builder after all evidence is collected.
