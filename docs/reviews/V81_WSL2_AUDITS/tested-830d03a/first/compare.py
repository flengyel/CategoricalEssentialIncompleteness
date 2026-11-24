from collections import defaultdict
from hashlib import sha256
from pathlib import Path
import json
import re
import subprocess

S = Path(__file__).resolve().parent
repo = Path(subprocess.check_output(["git", "rev-parse", "--show-toplevel"], cwd=S, text=True).strip())
GIT = '830d03a5adcf144a003feb36f88bd06e0c5b0cf5'
def gitfile(name):
    return subprocess.check_output(['git', 'show', GIT + ':' + name], cwd=repo)

def write_lines(name,lines):
    (S/name).write_text('\n'.join(lines)+'\n')

manifest=json.loads(gitfile('MANUSCRIPT_CURRENT.json'))
rows=[]
for m in manifest['files']:
    path=m['path']
    if path.endswith('.tex'):
        p=path.removeprefix('manuscript/latex/')
        blob=gitfile(path)
        same=blob==(S/'paper'/p).read_bytes()
        assert same and sha256(blob).hexdigest()==m['sha256'], p
        rows.append(f'{m["sha256"]}\t{p}\t{len(blob)} bytes\tmatched blind, commit, manifest')
assert len(rows)==25
write_lines('source-hashes.tsv',rows)
rs=[json.loads(l) for l in (S/'reading-order.jsonl').read_text().splitlines()]
claims={r['claim'] for r in rs if r['kind'] in {'theorem','proposition','corollary','definition','lemma'}}
active=gitfile('FORMALIZATION_STATUS_V81.md').decode()
numbered=active.split('## Numbered statements',1)[1]
current={m[1]:m[0] for m in re.findall(r'^\| ((?:Definition|Corollary|Lemma|Proposition|Theorem) [0-9A-Z]+\.\d+); `([^`]+)`',numbered,re.M)}
assert claims==set(current) and len(claims)==80
# Only use this crosswalk for candidate declaration names. All source bytes and Lean types
# and permitted dependencies are checked here and again against the current machine receipt.
locs=gitfile('docs/reviews/V81_PROOF_COMPARISONS/numbered-receipt.md').decode().split('### Section 3',1)[1]
indexed=defaultdict(list)
modules=set(); decls={}
for line in locs.splitlines():
    if not line.startswith('| ['):
        continue
    lab=re.search(r'\) `([^`]+)`',line)[1]
    for flag,name,url in re.findall(r'\b([CRSM]) \[`([^`]+)`\]\(([^)]+)\)',line):
        path,ln=url.removeprefix('../../../').split('#L'); lineno=int(ln)
        mod=path.removeprefix('Lean/').removesuffix('.lean').replace('/','.')
        assert gitfile(path)==(repo/path).read_bytes()
        modules.add(mod)
        if flag=='M':
            indexed[lab].append({'module':mod,'source':path,'line':lineno}); continue
        full=name.replace('LC.', 'CategoricalEssentialIncompleteness.LocalConnectedness.',1) if name.startswith('LC.') else name.replace('V46.','CategoricalEssentialIncompleteness.V46.',1)
        indexed[lab].append({'name':full,'module':mod,'source':path,'line':lineno})
        decls[full]=mod
assert set(indexed)==claims
write_lines('numbered-sources.jsonl',(json.dumps(dict(label=k,printed=current[k],entries=v),ensure_ascii=False) for k,v in indexed.items()))
write_lines('numbered-kernel.lean',[*(f'import {m}' for m in sorted(modules)), '','set_option pp.universes false', *(f'#check @{n}\n#print axioms {n}' for n in decls)])
print(f'{len(rows)} original TeX files, {len(claims)} numbered labels, {len(decls)} declarations, {len(modules)} imported modules')
