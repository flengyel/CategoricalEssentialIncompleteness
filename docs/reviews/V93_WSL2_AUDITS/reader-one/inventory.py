"""Rebuild the first reader's manuscript-only passage and statement inventory."""
import gzip, hashlib, json, re, subprocess
from pathlib import Path
sha='2269c9674e710a7032e6751e7db2473147aaaf96'
dest=Path(__file__).resolve().parent
order=[]; lines=[]; envs=[]; citations=[]
def read(fn):
    b=subprocess.check_output(['git','show',sha+':manuscript/latex/'+fn])
    data=b.decode(); order.append(dict(file=fn,sha256=hashlib.sha256(b).hexdigest(),lines=len(data.splitlines())))
    for n,s in enumerate(data.splitlines(),1):
        lines.append((fn,n,s))
        for child in re.findall(r'^\s*\\(?:input|include)\{([^}]+)\}',s):
            read(child if Path(child).suffix else child+'.tex')
read('main.tex')
sect=0; isapp=False; count=0
stored={}; rows=[]; links=[]
for f,n,s in lines:
    if r'\appendix' in s and f=='main.tex':
        isapp=True;sect=0
    if re.match(r'^\\section\{',s):
        sect+=1; count=0
    m=re.search(r'\\begin\{(lemma|proposition|theorem|corollary|definition)\}',s)
    if m:
        count+=1
        number=f'{chr(64+sect) if isapp else sect}.{count}'
        row={'number':number,'environment':m[1],'file':f,'start':n}
        rows.append(row); stored['row']=row
    if 'row' in stored:
        row=stored['row']
        if 'label' not in row:
            m=re.search(r'\\label\{([^}]+)\}',s)
            if m: row['label']=m[1]
        if f"\\end{{{row['environment']}}}" in s: row['end']=n; del stored['row']
    if r'\begin{proof}' in s and rows and rows[-1]['file']==f: rows[-1]['proof_start']=n
    if r'\end{proof}' in s and rows and rows[-1]['file']==f: rows[-1]['proof_end']=n
passages=[]; buf=[]; prev=None
def finish():
    if buf:
        fn,x=buf[0][:2]; txt='\n'.join(r[2] for r in buf)
        passages.append({'file':fn,'start':x,'end':buf[-1][1],'sha256':hashlib.sha256(txt.encode()).hexdigest()})
        for m in re.finditer(r'\\cite(?:\[([^\]]*)\])?\{([^}]+)\}',txt,re.S):
            for k in m[2].split(','):
                links.append({'file':fn,'line':x+txt[:m.start()].count('\n'),'key':k,'printed_locator':' '.join((m[1] or '').split())})
        buf.clear()
for item in lines:
    f,n,s=item
    if prev!=f or not s.strip(): finish()
    if s.strip(): buf.append(item)
    prev=f
finish()
for path,v in [('tex-inventory.json',{'commit':sha,'recursive_order':order}),('claims.json',rows),('citations.json',links)]:
    (dest/path).write_text(json.dumps(v,indent=2,ensure_ascii=False)+'\n')
(dest/'passages.json.gz').write_bytes(gzip.compress(json.dumps(passages,separators=(',',':')).encode(),mtime=0))
print(len(rows),len(passages),len(links))
