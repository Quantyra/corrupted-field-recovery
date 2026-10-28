#!/usr/bin/env bash
set -euo pipefail
run="$HOME/quantyra-cfr-runs/cfr-baseline-20261028T211424Z-5ddb91"
campaign="$HOME/quantyra-cfr-runs/cfr-lean430-c5ea-20261028"
mkdir -p "$run/logs"
exec > >(tee "$run/logs/runner.stdout.txt") 2> >(tee "$run/logs/runner.stderr.txt" >&2)
trap 'code=$?; echo "$code" > "$run/exit-code"; date -u +%FT%TZ > "$run/finished-utc"' EXIT
date -u +%FT%TZ > "$run/started-utc"
exec 9> "$campaign/lock"
flock -n 9 || exit 75
echo '3ab12bca1bca411c8d803d50042d1b2d3e4fc34a3f5219abe2430f7c5babc53b  '"$run/gcp_cfr_runner.py" | sha256sum -c -
CFR_GCP_RUN=cfr-baseline-20261028T211424Z-5ddb91 python3 "$run/gcp_cfr_runner.py" "$run" "$campaign"
