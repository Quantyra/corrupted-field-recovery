"""Fail closed until the requested complete certification and package are ready."""
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]


def main():
    failures = []
    required = ['manuscript/main.tex', 'manuscript/main.pdf', 'CITATION.cff',
                'LICENSE', 'LICENSES/CC-BY-4.0.txt', 'PROVENANCE.md',
                'src/recovery.py', 'tests/check_recovery.py', 'lean-toolchain',
                'lakefile.toml', 'lake-manifest.json', 'checks/Audit.lean']
    failures += [f'missing file: {p}' for p in required if not (ROOT/p).is_file()]
    coverage = json.loads((ROOT/'formal/coverage.json').read_text(encoding='utf-8'))
    if not coverage['complete']:
        failures.append('complete Lean certification is not established')
    failures += [f'formal obligation {o["id"]}: {o["status"]}'
                 for o in coverage['obligations'] if o.get('required', True) and o['status'] != 'proved']
    audit_path = ROOT/'artifacts/lean-audit.log'
    audit_text = audit_path.read_text(encoding='utf-8') if audit_path.exists() else ''
    for obligation in coverage['obligations']:
        if obligation.get('required', True) and obligation['status'] == 'proved':
            exports = obligation.get('exports', [])
            if not exports:
                failures.append(f'no audited declaration for proved obligation: {obligation["id"]}')
            for declaration in exports:
                if f"'{declaration}' depends on axioms:" not in audit_text:
                    failures.append(f'missing axiom report: {declaration}')
    for receipt in ['recovery-checks.json', 'lean-checks.json', 'pdf-checks.json']:
        path = ROOT/'artifacts'/receipt
        if not path.is_file():
            failures.append(f'missing receipt: {receipt}')
            continue
        data = json.loads(path.read_text(encoding='utf-8'))
        if receipt == 'recovery-checks.json':
            if data.get('status') != 'passed':
                failures.append('recovery checks did not pass')
            for source, expected in data['source_sha256'].items():
                if hashlib.sha256((ROOT/source).read_bytes()).hexdigest() != expected:
                    failures.append(f'stale test evidence: {source}')
        elif receipt == 'lean-checks.json':
            if data.get('status') != 'passed':
                failures.append('Lean build and audit did not both pass')
            for source, expected in data.get('source_sha256', {}).items():
                if hashlib.sha256((ROOT/source).read_bytes()).hexdigest() != expected:
                    failures.append(f'stale Lean evidence: {source}')
        elif receipt == 'pdf-checks.json':
            for source, key in [('manuscript/main.pdf', 'pdf_sha256'),
                                ('manuscript/main.tex', 'source_sha256')]:
                if hashlib.sha256((ROOT/source).read_bytes()).hexdigest() != data[key]:
                    failures.append(f'stale PDF evidence: {source}')
            if data.get('visual_inspection') != 'passed':
                failures.append('rendered PDF inspection is not recorded as passed')
    result = dict(ready=not failures, failures=failures,
                  publication_authorized=True,
                  note='No additional human publication permission is required. Mathematical and formal work remains mandatory.')
    print(json.dumps(result, indent=2))
    return int(bool(failures))


if __name__ == '__main__':
    sys.exit(main())
