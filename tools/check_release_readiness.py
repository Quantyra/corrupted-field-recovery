"""Check preprint evidence; optionally require complete Lean certification."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
REQUIRED_OBLIGATIONS = {'input_model', 'four_contractions', 'two_translate_image',
                        'sampling_bounds', 'bounded_constructor', 'certificate',
                        'costs', 'main_theorem'}
MINIMUM_AUDIT = {
    'CorruptedFieldRecovery.imbalance_add',
    'CorruptedFieldRecovery.balanced_cancels',
    'CorruptedFieldRecovery.imbalance_mode_le',
    'CorruptedFieldRecovery.two_translate_modeImage',
    'CorruptedFieldRecovery.recovery_modeImage',
    'CorruptedFieldRecovery.joint_surjective_of_disjoint_duals',
    'CorruptedFieldRecovery.two_translate_of_disjoint',
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--require-complete-lean', action='store_true')
    args = parser.parse_args()
    failures = []

    def read_json(name):
        try:
            value = json.loads((ROOT/name).read_text(encoding='utf-8'))
            if not isinstance(value, dict):
                raise ValueError('expected object')
            return value
        except (OSError, ValueError) as exc:
            failures.append(f'invalid or missing {name}: {exc}')
            return {}

    def check_hash(path, expected, label):
        try:
            if not isinstance(path, str) or not isinstance(expected, str):
                raise ValueError('missing path or hash')
            resolved = (ROOT/path).resolve()
            if not resolved.is_relative_to(ROOT.resolve()) or not resolved.is_file():
                raise ValueError('missing or outside repository')
            if not re.fullmatch(r'[0-9a-f]{64}', expected):
                raise ValueError('invalid SHA-256')
            if hashlib.sha256(resolved.read_bytes()).hexdigest() != expected:
                raise ValueError('hash mismatch')
        except (OSError, ValueError) as exc:
            failures.append(f'{label}: {path}: {exc}')

    required = ['manuscript/main.tex', 'manuscript/main.pdf', 'CITATION.cff', '.zenodo.json',
                'LICENSE', 'LICENSES/CC-BY-4.0.txt', 'PROVENANCE.md',
                'src/recovery.py', 'tests/check_recovery.py', 'lean-toolchain',
                'lakefile.toml', 'lake-manifest.json', 'checks/Audit.lean']
    failures += [f'missing file: {p}' for p in required if not (ROOT/p).is_file()]
    coverage = read_json('formal/coverage.json')
    obligations = coverage.get('obligations', [])
    if not isinstance(obligations, list) or not obligations:
        failures.append('formal obligations missing or invalid')
        obligations = []
    incomplete = [f'formal obligation {o.get("id")}: {o.get("status")}'
                  for o in obligations if isinstance(o, dict)
                  and o.get('required', True) and o.get('status') != 'proved']
    if any(not isinstance(o, dict) for o in obligations):
        failures.append('invalid formal obligation')
    if type(coverage.get('complete')) is not bool:
        failures.append('formal coverage complete flag missing or invalid')
    elif coverage['complete'] and incomplete:
        failures.append('complete Lean coverage conflicts with incomplete obligations')
    if args.require_complete_lean:
        required_ids = [o.get('id') for o in obligations if isinstance(o, dict)
                        and o.get('required', True)]
        if not REQUIRED_OBLIGATIONS <= set(required_ids) or len(required_ids) != len(set(required_ids)):
            failures.append('mandatory manuscript obligations missing, optionalized, or duplicated')
        if coverage.get('complete') is not True:
            failures.append('complete Lean certification is not established')
        failures.extend(incomplete)

    recovery = read_json('artifacts/recovery-checks.json')
    if recovery.get('status') != 'passed':
        failures.append('recovery checks did not pass')
    recovery_hashes = recovery.get('source_sha256', {})
    if not isinstance(recovery_hashes, dict):
        recovery_hashes = {}
    for source in ['src/recovery.py', 'tests/check_recovery.py']:
        if source not in recovery_hashes:
            failures.append(f'missing test evidence: {source}')
    for source, expected in recovery_hashes.items():
        check_hash(source, expected, 'stale test evidence')

    lean = read_json('artifacts/lean-checks.json')
    if lean.get('status') != 'passed':
        failures.append('Lean build and audit did not both pass')
    lean_hashes = lean.get('source_sha256', {})
    if not isinstance(lean_hashes, dict):
        lean_hashes = {}
    expected_sources = {'CorruptedFieldRecovery.lean', 'checks/Audit.lean',
                        'lakefile.toml', 'lake-manifest.json', 'lean-toolchain',
                        'tools/check_lean.py'}
    expected_sources.update(p.relative_to(ROOT).as_posix()
                            for p in (ROOT/'CorruptedFieldRecovery').glob('*.lean'))
    for source in expected_sources - lean_hashes.keys():
        failures.append(f'missing Lean source evidence: {source}')
    for source, expected in lean_hashes.items():
        check_hash(source, expected, 'stale Lean evidence')
    log_hashes = lean.get('log_sha256', {})
    if not isinstance(log_hashes, dict):
        log_hashes = {}
    for log in ['artifacts/lean-build.log', 'artifacts/lean-audit.log']:
        check_hash(log, log_hashes.get(log), 'stale Lean log')
    commands = lean.get('commands', [])
    expected_commands = [(['lake', 'build', 'CorruptedFieldRecovery'], 'artifacts/lean-build.log'),
                         (['lake', 'env', 'lean', 'checks/Audit.lean'], 'artifacts/lean-audit.log')]
    if not isinstance(commands, list) or len(commands) != len(expected_commands) or any(
            not isinstance(entry, dict) or entry.get('command') != command
            or entry.get('exit_code') != 0 or entry.get('log') != log
            for entry, (command, log) in zip(commands, expected_commands)):
        failures.append('Lean command evidence missing or unsuccessful')
    try:
        audit_source = (ROOT/'checks/Audit.lean').read_text(encoding='utf-8')
        audit_text = (ROOT/'artifacts/lean-audit.log').read_text(encoding='utf-8')
        requested = re.findall(r'^#print axioms\s+(\S+)\s*$', audit_source, re.M)
        reports = re.findall(r"^'([^']+)' depends on axioms:\s*\[([^\]]*)\]", audit_text, re.M)
        names = [name for name, _ in reports]
        axioms = {a.strip() for _, values in reports for a in values.split(',') if a.strip()}
        if (not MINIMUM_AUDIT <= set(requested) or len(requested) != len(set(requested))
                or len(names) != len(set(names)) or set(names) != set(requested)):
            failures.append('Lean audit declarations missing, duplicate, or unreported')
        if not axioms <= ALLOWED_AXIOMS:
            failures.append(f'disallowed Lean axioms: {sorted(axioms - ALLOWED_AXIOMS)}')
        if sorted(names) != lean.get('audited_declarations') or sorted(axioms) != lean.get('reported_axioms'):
            failures.append('Lean audit receipt does not match audit log')
        for obligation in obligations:
            if isinstance(obligation, dict) and obligation.get('status') == 'proved':
                exports = obligation.get('exports')
                if not isinstance(exports, list) or not exports or any(e not in names for e in exports):
                    failures.append(f'proved obligation lacks audited exports: {obligation.get("id")}')
    except OSError as exc:
        failures.append(f'cannot read Lean audit: {exc}')

    pdf = read_json('artifacts/pdf-checks.json')
    for source, key in [('manuscript/main.pdf', 'pdf_sha256'),
                        ('manuscript/main.tex', 'source_sha256')]:
        check_hash(source, pdf.get(key), 'stale PDF evidence')
    if pdf.get('visual_inspection') != 'passed':
        failures.append('rendered PDF inspection is not recorded as passed')

    review = read_json('artifacts/multimodel-review.json')
    if review.get('status') != 'completed':
        failures.append('multimodel review not completed')
    if not isinstance(review.get('baseline_commit'), str) or not re.fullmatch(
            r'[0-9a-f]{40}', review['baseline_commit']):
        failures.append('invalid review baseline commit')
    if review.get('unresolved_blocking_findings') != []:
        failures.append('unresolved or unreported blocking review findings')
    check_hash('manuscript/main.tex', review.get('revised_manuscript_sha256'),
               'stale revised-manuscript review')
    reviews = review.get('reviews')
    if not isinstance(reviews, list) or len(reviews) < 3 or any(not isinstance(r, dict) for r in reviews):
        failures.append('at least three model reviews are required')
    else:
        models = [r.get('model') for r in reviews]
        paths = [r.get('report') for r in reviews]
        if (any(not isinstance(m, str) or not m.strip() for m in models)
                or len(set(models)) != len(models) or any(not isinstance(p, str) for p in paths)
                or len(set(paths)) != len(paths)):
            failures.append('review models and report paths must be distinct')
        for item in reviews:
            check_hash(item.get('report'), item.get('sha256'), 'review evidence')
    check_hash(review.get('disposition'), review.get('disposition_sha256'), 'review disposition')

    result = dict(ready=not failures, failures=failures,
                  require_complete_lean=args.require_complete_lean,
                  complete_lean=coverage.get('complete') is True,
                  incomplete_formal_obligations=incomplete,
                  publication_authorized=True,
                  note='Partial Lean evidence does not certify the main theorem or Python implementation.')
    print(json.dumps(result, indent=2))
    return int(bool(failures))


if __name__ == '__main__':
    sys.exit(main())
