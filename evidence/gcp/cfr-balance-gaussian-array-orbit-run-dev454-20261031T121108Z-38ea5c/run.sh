#!/usr/bin/env bash
set -euo pipefail
run="$HOME/quantyra-cfr-runs/cfr-balance-gaussian-array-orbit-run-dev454-20261031T121108Z-38ea5c"
campaign="$HOME/quantyra-cfr-runs/cfr-lean430-c5ea-isolated-20261028a"
mkdir -p "$run/logs"
exec > >(tee "$run/logs/runner.stdout.txt") 2> >(tee "$run/logs/runner.stderr.txt" >&2)
trap 'code=$?; echo "$code" > "$run/exit-code"; date -u +%FT%TZ > "$run/finished-utc"' EXIT
date -u +%FT%TZ > "$run/started-utc"
exec 9> "$campaign/lock"
flock -n 9 || exit 75
echo 'b8b5779c34ff0d8da07916a6376f920949c9dd600019d19a878285d0172ec005  '"$run/gcp_cfr_runner.py" | sha256sum -c -
CFR_GCP_RUN=cfr-balance-gaussian-array-orbit-run-dev454-20261031T121108Z-38ea5c python3 "$run/gcp_cfr_runner.py" "$run" "$campaign"
