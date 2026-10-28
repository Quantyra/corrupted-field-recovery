# CFR GCP campaign checkpoint

Prepared 28 October 2026. **No CFR cloud compiler has run yet.** The existing
saved local Lean receipts remain historical supplementary evidence, not a new
GCP certification result. `formal/coverage.json` and the root/audit exports
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

The non-Lean readiness command was rerun and its accurately false result now
appears in `artifacts/release-readiness.json`; it reports missing compiled
evidence for all three drafts. The prior working-tree result is preserved under
`cfr-readiness-20261028T213927Z-8d63e3` alongside the exact new output, command
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

After the user confirms reauthentication, resume with the existing handles:

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
