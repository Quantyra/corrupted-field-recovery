import gcp_cfr as c
import hashlib
out = c.EVIDENCE / 'cfr-raw-factor-irreducible-dev25-20261029T140217Z-990ff3'
run = '$HOME/quantyra-cfr-runs/'+out.name
raw = c.ssh('set -eu\nrun="'+run+'"\n'
    'for marker in runner-pid launch.log started-utc exit-code current-stage logs terminal-receipt.json; do test ! -e "$run/$marker"; done\n'
    'if pgrep -x lean || pgrep -x lake || pgrep -af "[g]cp_cfr_runner.py|[q]uantyra-cfr-runs/.*/run.sh"; then exit 74; fi\n'
    'sha256sum "$run/capture-manifest.json" "$run/inputs.tar.gz"\n', out, c.unique('never-started-proof'))
assert raw.decode().splitlines()[0].split()[0] == hashlib.sha256((out/'capture-manifest.json').read_bytes()).hexdigest()
assert raw.decode().splitlines()[1].split()[0] == hashlib.sha256((out/'inputs.tar.gz').read_bytes()).hexdigest()
c.save(out/'never-started-resolution.json', dict(run=out.name, instance=c.VM, utc=c.utc(), never_started=True,
    capture_manifest_sha256=hashlib.sha256((out/'capture-manifest.json').read_bytes()).hexdigest(),
    evidence_sha256=hashlib.sha256(raw).hexdigest(), conclusion='No remote launch markers or runner/compiler processes; no compiler outcome exists. Never relaunch this handle.'))
