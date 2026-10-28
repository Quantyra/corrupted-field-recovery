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
| `cfr-binary-bridge-dev03-20261028T212244Z-2ab65e` | Matched successor tuple after that repair | Captured; development build pending |

Every capture preserves exact offered bytes, a SHA-256 archive digest, source
digests, UTF-8/no-BOM validation and the complete pinned dependency revisions.
Capture acknowledgments permit authors to edit successors; each compilation
will use its own immutable archive, never a live author worktree.

The current `BinaryTensor.lean` and `Bridge.lean` files are **uncompiled drafts**.
The latest tuple is binary source SHA-256
`9bf4fd8a01b74705243bdbe1d15fc28dffb99813720632b37d851a0efb61bc0a`
and bridge SHA-256
`99c60d832f9d52b9fa5c15a0fd5291c70bd082af92a35b5637325fec314c2db2`.
The bridge contains valid Lean Unicode; an early author message calling it
ASCII-only was inaccurate. Neither draft closes a manuscript coverage item.

The non-Lean readiness command was rerun and its accurately false result now
appears in `artifacts/release-readiness.json`; it reports missing compiled
evidence for the two drafts. The former working-tree result is preserved under
`cfr-readiness-20261028T212231Z-2539d3` alongside the exact new output, command
and exit code. This working-tree change does not alter the separately verified
first archive or its DOI.

The isolated cloud controls and cache/ownership policy are documented in
`tools/gcp-README.md`. Python syntax and immutable archive-member/hash checks
were performed locally without invoking Lean. The remote runner is prepared
but not yet cloud-tested. Full type/axiom checks for the new declarations will
be captured at acceptance, in addition to focused development builds.

Remaining to-do list: renew GCP login; observe live VM ownership/state; run and
preserve the baseline; compile the matched draft tuple, route diagnostics and
capture repairs; continue the selected complete-manuscript milestones.
