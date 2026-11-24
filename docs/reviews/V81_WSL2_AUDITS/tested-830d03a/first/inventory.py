from pathlib import Path
import re, json, hashlib
p=Path(__file__).resolve().parent/'paper'
base=p.parent
units=[]; files=[]; coverage={}
include=re.compile(r'^\\input\{([^}]+)\}$'); title=re.compile(r'^\\(?:sub)*section\{(.*)\}')
stmt=re.compile(r'\\begin\{(definition|theorem|lemma|proposition|corollary)\}')
ctx={'title':'Front matter','proof':'','theorem':'','last':''}
def read(file):
 files.append(file); lines=(p/file).read_text().splitlines(); coverage[file]=set(); start=0; acc=[]
 def put():
  nonlocal start,acc
  if not acc: return
  raw='\n'.join(acc); more=ctx['title']; st=stmt.search(raw); labels=re.findall(r'\\label\{([^}]+)\}',raw); refs=re.findall(r'\\(?:ref|eqref)\{([^}]+)\}',raw); citations=re.findall(r'\\cite(?:\[[^\]]*\])?\{([^}]+)\}',raw); begin=bool(re.search(r'\\begin\{proof\}',raw)); end=bool(re.search(r'\\end\{proof\}',raw)); t=title.search(raw)
  if t: ctx['title']=t[1].split('}\\label')[0]; ctx['last']=''
  if st:
   ll=[v for v in labels if v.split(':')[0] in {'lem','def','prop','cor','thm'}]; ctx['theorem']=ll[0] if ll else st[1];ctx['last']=ctx['theorem']
  if begin: ctx['proof']=ctx['last']
  kind= ('front matter' if file in {'main.tex','preamble.tex'} else 'bibliographic entry' if file=='bibliography.tex' else 'section' if t else st[1] if st else 'proof' if ctx['proof'] else 'prose or display')
  if file=='abstract.tex':kind='abstract assertion'
  units.append(dict(id=f'R{len(units)+1:04d}',path=file,line=start,end=start+len(acc)-1,kind=kind,section=ctx['title'],claim=ctx['theorem'] or ctx['proof'] or None,references=refs,citations=[k for s in citations for k in s.split(',')],labels=labels,source=raw));coverage[file].update(range(start,start+len(acc)))
  if end:ctx['proof']=''
  if re.search(r'\\end\{(definition|theorem|lemma|proposition|corollary)\}',raw):ctx['theorem']=''
  acc=[]
 for n,line in enumerate(lines,1):
  m=include.fullmatch(line.strip())
  if m:
   put();coverage[file].add(n);read(m[1]);continue
  if not line.strip():put();continue
  if title.match(line) or stmt.match(line) or line.startswith('\\begin{proof}') or line.startswith('\\bibitem'):put()
  if not acc:start=n
  acc.append(line)
  if re.search(r'\\end\{(definition|theorem|lemma|proposition|corollary|proof)\}',line):put()
 put()
 for i,l in enumerate(lines,1):assert i in coverage[file] or not l.strip(),(file,i)
read('main.tex')
assert set(files)=={str(f.relative_to(p)) for f in p.rglob('*.tex')} and len(files)==25
(base/'reading-order.jsonl').write_text(''.join(json.dumps(u,ensure_ascii=False)+'\n' for u in units))
(base/'paper-inputs.sha256').write_text(''.join(hashlib.sha256((p/f).read_bytes()).hexdigest()+'  paper/'+f+'\n' for f in sorted(files)))
print(len(files),len(units),{k:sum(u['kind']==k for u in units) for k in sorted({u['kind'] for u in units})})
