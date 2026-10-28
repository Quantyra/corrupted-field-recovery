"""Extract page diagnostics and render every page for human/assistant inspection."""
from pathlib import Path
import hashlib
import json
import sys

# The optional argument is a site-packages directory for embedded Python.
if len(sys.argv) > 1:
    sys.path.insert(0, sys.argv[1])
import pymupdf

ROOT = Path(__file__).resolve().parents[1]
source = ROOT/'manuscript/main.pdf'
output = ROOT/'tmp/pdf-pages'
output.mkdir(parents=True, exist_ok=True)
doc = pymupdf.open(source)
pages = []
for i, page in enumerate(doc):
    path = output/f'page-{i+1}.png'
    page.get_pixmap(matrix=pymupdf.Matrix(1.1, 1.1)).save(path)
    text = page.get_text()
    pages.append(dict(page=i+1, characters=len(text), links=len(page.get_links()),
                      fonts=[list(f[:4]) for f in page.get_fonts()],
                      outside_page_blocks=[list(b[:4]) for b in page.get_text('blocks')
                                           if b[0] < 0 or b[1] < 0 or b[2] > page.rect.width
                                           or b[3] > page.rect.height]))
    assert text.strip() and '??' not in text
    assert not pages[-1]['outside_page_blocks']
receipt = dict(pdf_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
               source_sha256=hashlib.sha256((ROOT/'manuscript/main.tex').read_bytes()).hexdigest(),
               renderer=f'PyMuPDF {pymupdf.VersionBind}', pages=pages,
               visual_inspection='Pending review of rendered page images; rendering is not inspection.')
(ROOT/'artifacts/pdf-checks.json').write_text(json.dumps(receipt, indent=2)+'\n', encoding='utf-8')
print(json.dumps(dict(pages=len(doc), pdf_sha256=receipt['pdf_sha256'], output=str(output))))
