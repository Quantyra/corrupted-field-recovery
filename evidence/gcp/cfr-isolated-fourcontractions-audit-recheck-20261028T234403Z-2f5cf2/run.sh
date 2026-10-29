#!/usr/bin/env bash
set -euo pipefail
run="$HOME/quantyra-cfr-runs/cfr-isolated-fourcontractions-audit-recheck-20261028T234403Z-2f5cf2"
campaign="$HOME/quantyra-cfr-runs/cfr-lean430-c5ea-isolated-20261028a"
mkdir -p "$run/logs"
exec > >(tee "$run/logs/runner.stdout.txt") 2> >(tee "$run/logs/runner.stderr.txt" >&2)
trap 'code=$?; echo "$code" > "$run/exit-code"; date -u +%FT%TZ > "$run/finished-utc"' EXIT
date -u +%FT%TZ > "$run/started-utc"
exec 9> "$campaign/lock"
flock -n 9 || exit 75
echo '867a82b188e7966679bb9979b7bf2be9baa8b4995eed5733c658708135da6ae6  '"$run/gcp_cfr_runner.py" | sha256sum -c -
CFR_GCP_RUN=cfr-isolated-fourcontractions-audit-recheck-20261028T234403Z-2f5cf2 python3 "$run/gcp_cfr_runner.py" "$run" "$campaign"
