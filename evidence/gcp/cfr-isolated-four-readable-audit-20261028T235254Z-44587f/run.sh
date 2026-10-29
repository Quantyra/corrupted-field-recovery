#!/usr/bin/env bash
set -euo pipefail
run="$HOME/quantyra-cfr-runs/cfr-isolated-four-readable-audit-20261028T235254Z-44587f"
campaign="$HOME/quantyra-cfr-runs/cfr-lean430-c5ea-isolated-20261028a"
mkdir -p "$run/logs"
exec > >(tee "$run/logs/runner.stdout.txt") 2> >(tee "$run/logs/runner.stderr.txt" >&2)
trap 'code=$?; echo "$code" > "$run/exit-code"; date -u +%FT%TZ > "$run/finished-utc"' EXIT
date -u +%FT%TZ > "$run/started-utc"
exec 9> "$campaign/lock"
flock -n 9 || exit 75
echo 'cdd96d1c4786d5810c89caf2ecd313dba38d774f67d5213d48958ed0d82c2a26  '"$run/gcp_cfr_runner.py" | sha256sum -c -
CFR_GCP_RUN=cfr-isolated-four-readable-audit-20261028T235254Z-44587f python3 "$run/gcp_cfr_runner.py" "$run" "$campaign"
