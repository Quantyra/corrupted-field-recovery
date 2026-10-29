import gcp_cfr as c
from argparse import Namespace
import json
old=json.loads((c.EVIDENCE/'cfr-raw-factor-irreducible-dev25-20261029T140217Z-990ff3'/'capture-manifest.json').read_text())
c.capture(Namespace(label='raw-factor-irreducible-dev27',commit=None,target=old['targets'],no_audit=False,audit_export=old['audited_exports']))
