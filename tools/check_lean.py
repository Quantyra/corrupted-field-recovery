"""Build and audit the present Lean library; never infer full coverage from a build."""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]


def main():
    if hasattr(sys.stdout, 'reconfigure'):
        sys.stdout.reconfigure(encoding='utf-8')
    sources = [ROOT/'CorruptedFieldRecovery.lean', *sorted((ROOT/'CorruptedFieldRecovery').glob('*.lean')),
               ROOT/'checks/Audit.lean', ROOT/'lakefile.toml', ROOT/'lake-manifest.json', ROOT/'lean-toolchain',
               Path(__file__).resolve()]
    for path in sources:
        if path.suffix == '.lean':
            text = re.sub(r'/\-.*?\-/', '', path.read_text(encoding='utf-8'), flags=re.S)
            text = re.sub(r'--[^\n]*', '', text)
            if re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b', text):
                raise RuntimeError(f'forbidden proof shortcut in {path.name}')
    artifacts = ROOT/'artifacts'
    artifacts.mkdir(exist_ok=True)
    receipt = dict(status='failed', toolchain=(ROOT/'lean-toolchain').read_text().strip(),
                   source_sha256={str(p.relative_to(ROOT)).replace('\\', '/'):
                                  hashlib.sha256(p.read_bytes()).hexdigest() for p in sources},
                   scope='Intermediate defect-image lemmas only; not complete certification', commands=[])
    for label, args in [('build', ['lake', 'build', 'CorruptedFieldRecovery']),
                        ('audit', ['lake', 'env', 'lean', 'checks/Audit.lean'])]:
        print('Running', ' '.join(args), flush=True)
        result = subprocess.run(args, cwd=ROOT, text=True, encoding='utf-8', errors='replace',
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=3600)
        (artifacts/f'lean-{label}.log').write_text(result.stdout, encoding='utf-8')
        receipt['commands'].append(dict(command=args, exit_code=result.returncode,
                                       log=f'artifacts/lean-{label}.log'))
        print(result.stdout, flush=True)
        if result.returncode:
            break
        if label == 'audit':
            reports = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', result.stdout)
            allowed = {'propext', 'Classical.choice', 'Quot.sound'}
            found = {a.strip() for report in reports for a in report.split(',') if a.strip()}
            if len(reports) != 7 or not found <= allowed:
                raise RuntimeError(f'invalid axiom audit: {reports}')
            receipt['reported_axioms'] = sorted(found)
            receipt['status'] = 'passed'
    (artifacts/'lean-checks.json').write_text(json.dumps(receipt, indent=2)+'\n', encoding='utf-8')
    return int(receipt['status'] != 'passed')


if __name__ == '__main__':
    sys.exit(main())
