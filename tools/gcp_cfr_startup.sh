#!/usr/bin/env bash
set -euo pipefail
exec > >(tee -a /var/log/quantyra-cfr-bootstrap.log) 2>&1
apt-get update
DEBIAN_FRONTEND=noninteractive apt-get install -y git curl build-essential zstd jq time ca-certificates
mkdir -p /opt/quantyra
if ! test -x /opt/quantyra/lean-4.30.0-linux/bin/lean; then
  curl --fail --location --retry 3 --max-time 1200 \
    https://github.com/leanprover/lean4/releases/download/v4.30.0/lean-4.30.0-linux.tar.zst \
    -o /opt/quantyra/lean-4.30.0-linux.tar.zst
  echo '4dad74141c2c119ca1aa626656be83b8e14238afba97271fd7bf1eb3f081b319  /opt/quantyra/lean-4.30.0-linux.tar.zst' | sha256sum -c -
  tar --zstd -xf /opt/quantyra/lean-4.30.0-linux.tar.zst -C /opt/quantyra
fi
# No idle timer: uploads and prelaunch handles must not trigger shutdown.
# GCE enforces the explicit four-hour per-start STOP limit.
touch /var/lib/quantyra-cfr-builder-ready
