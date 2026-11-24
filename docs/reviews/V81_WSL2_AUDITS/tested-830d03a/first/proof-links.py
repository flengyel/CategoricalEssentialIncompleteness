from pathlib import Path
from hashlib import sha256
import re, subprocess, json
s=Path(__file__).resolve().parent;repo=Path(subprocess.check_output(['git','rev-parse','--show-toplevel'],cwd=s,text=True).strip()); sha='830d03a5adcf144a003feb36f88bd06e0c5b0cf5'; tag='cei-v72-palomar-v3'
txt=(s/'paper/appendices/e-reading-lean-proofs.tex').read_text();out=[]
for m in re.finditer(r'\\CEIproof\{([^}]+)\}\{L(\d+)-L(\d+)\}',txt):
 file='Lean/'+m[1]+'.lean';lo,hi=map(int,m.groups()[1:]);a=subprocess.check_output(['git','show',tag+':'+file],cwd=repo); b=subprocess.check_output(['git','show',sha+':'+file],cwd=repo);
 one=a.splitlines(keepends=True)[lo-1:hi];two=b.splitlines(keepends=True)[lo-1:hi]
 out.append({'line':txt[:m.start()].count('\n')+1,'file':file,'start':lo,'end':hi,'span_at_tag':sha256(b''.join(one)).hexdigest(),'span_at_tested_commit':sha256(b''.join(two)).hexdigest(),'same_span':one==two,'same_file':a==b})
(s/'appendix-e-links.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n');print(len(out),sum(r['same_span'] for r in out),sum(r['same_file'] for r in out));print([(r['line'],r['file'].split('/')[-1]) for r in out if not r['same_span']]);
