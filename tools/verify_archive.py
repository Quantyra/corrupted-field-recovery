"""Verify a public Zenodo record against every file in a local Git release tag.

Usage: python tools/verify_archive.py RECORD_ID [TAG]
Downloads public metadata/archive only; does not publish or modify a record.
"""
from datetime import datetime, timezone
import hashlib
import io
import json
from pathlib import Path
import subprocess
import sys
from urllib.request import Request, urlopen
from zipfile import ZipFile

ROOT = Path(__file__).resolve().parents[1]


def fetch(url):
    with urlopen(Request(url, headers={'User-Agent': 'Quantyra-archive-verification/0.1'}),
                 timeout=90) as response:
        return response.read()


def main():
    record_id = sys.argv[1]
    if not record_id.isdigit():
        raise ValueError('expected a numeric public Zenodo record ID')
    tag = sys.argv[2] if len(sys.argv) > 2 else 'v0.1.0'
    commit = subprocess.check_output(['git', 'rev-parse', '--verify', tag+'^{commit}'],
                                     cwd=ROOT, text=True).strip()
    local = subprocess.check_output(['git', 'archive', '--format=zip', tag], cwd=ROOT)
    record = json.loads(fetch('https://zenodo.org/api/records/'+record_id))
    metadata = record['metadata']
    if metadata.get('version') != tag.removeprefix('v'):
        raise ValueError('Zenodo version differs from requested Git tag')
    files = record['files']
    if len(files) != 1 or not files[0]['key'].endswith('.zip'):
        raise ValueError('expected the single GitHub source archive; inspect this record manually')
    entry = files[0]
    archive = fetch(entry['links']['self'])
    algorithm, expected = entry['checksum'].split(':', 1)
    if hashlib.new(algorithm, archive).hexdigest() != expected:
        raise ValueError('archive checksum does not match public metadata')
    with ZipFile(io.BytesIO(local)) as ours, ZipFile(io.BytesIO(archive)) as remote:
        actual = {name.split('/', 1)[1]: remote.read(name)
                  for name in remote.namelist() if not name.endswith('/')}
        wanted = {name: ours.read(name) for name in ours.namelist() if not name.endswith('/')}
    if actual.keys() != wanted.keys():
        raise ValueError('archive file inventory differs from Git tag')
    mismatch = [name for name in wanted if actual[name] != wanted[name]]
    if mismatch:
        raise ValueError('archive bytes differ: '+', '.join(mismatch))
    receipt = dict(status='verified', checked_at=datetime.now(timezone.utc).isoformat(),
                   record_id=record_id, version_doi=record['doi'],
                   concept_doi=record['conceptdoi'], tag=tag, commit=commit,
                   record_url='https://zenodo.org/records/'+record_id,
                   title=metadata['title'], version=metadata['version'],
                   creators=metadata['creators'], resource_type=metadata['resource_type'],
                   license=metadata['license'], archive_file=entry['key'],
                   archive_checksum=entry['checksum'], archive_bytes=len(archive),
                   archive_sha256=hashlib.sha256(archive).hexdigest(),
                   matched_files=len(wanted),
                   file_sha256={name: hashlib.sha256(data).hexdigest()
                                for name, data in sorted(actual.items())},
                   method='Public record and checksum; byte-for-byte comparison of every archived file against git archive of the named tag.')
    (ROOT/'artifacts/zenodo-archive.json').write_text(json.dumps(receipt, indent=2)+'\n',
                                                   encoding='utf-8', newline='\n')
    print(json.dumps({k: v for k, v in receipt.items() if k != 'file_sha256'}, indent=2))


if __name__ == '__main__':
    main()
