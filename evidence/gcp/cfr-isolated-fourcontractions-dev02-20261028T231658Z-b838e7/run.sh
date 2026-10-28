#!/usr/bin/env bash
set -euo pipefail
run="$HOME/quantyra-cfr-runs/cfr-isolated-fourcontractions-dev02-20261028T231658Z-b838e7"
campaign="$HOME/quantyra-cfr-runs/cfr-lean430-c5ea-isolated-20261028a"
mkdir -p "$run/logs"
exec > >(tee "$run/logs/runner.stdout.txt") 2> >(tee "$run/logs/runner.stderr.txt" >&2)
trap 'code=$?; echo "$code" > "$run/exit-code"; date -u +%FT%TZ > "$run/finished-utc"' EXIT
date -u +%FT%TZ > "$run/started-utc"
exec 9> "$campaign/lock"
flock -n 9 || exit 75
echo 'e0bf53e6d0725487975f3eeba18b252bbfc7ac74ce72f1aff2b20e15cfcb0a1b  '"$run/gcp_cfr_runner.py" | sha256sum -c -
CFR_GCP_RUN=cfr-isolated-fourcontractions-dev02-20261028T231658Z-b838e7 python3 "$run/gcp_cfr_runner.py" "$run" "$campaign"
