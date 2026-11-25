"""Reindex the manuscript-first reading, locate checked proof steps, and verify the Appendix E links."""
import difflib, functools, gzip, hashlib, json, re, subprocess, sys
from pathlib import Path
root = Path(sys.argv[1]).resolve()
out = Path(__file__).resolve().parent
new = '2269c9674e710a7032e6751e7db2473147aaaf96'
old = 'b37f8908435a4c2991af5b95de4645980ac60a05'
@functools.cache
def blob(rev, path):
    return subprocess.check_output(['git','show',rev+':'+path], cwd=root)
@functools.cache
def lines(rev,path): return blob(rev,path).decode().splitlines()
def gz(path, doc): (out/path).write_bytes(gzip.compress(json.dumps(doc,ensure_ascii=False,separators=(',',':')).encode(),mtime=0))
def get(path): return json.loads((out/path).read_bytes())
def indexed(name): return json.loads(gzip.decompress(blob(new,'docs/reviews/V84_WSL2_AUDITS/reader-one/'+name+'.json.gz')))
@functools.cache
def line_map(path, a, b):
    src=lines(a,path);dst=lines(b,path); result={}
    for tag, x,y,u,v in difflib.SequenceMatcher(None,src,dst,autojunk=False).get_opcodes():
        if tag=='equal':
            for i in range(x,y): result[i+1]=[u+1+i-x]
        elif tag=='replace':
            for i in range(x,y): result[i+1]=list(range(u+1,v+1))
        else:
            for i in range(x,y): result[i+1]=[]
    return result
claims=get('claims.json'); citations=get('citations.json'); readings=(out/'reconstruction.md').read_text().splitlines()
meta=indexed('claim-declarations'); prev=indexed('inventory'); ds=meta['declaration_sources']; new_decl={}
for name, src in ds.items():
    path=src['source']; ln=src['line']; nls=line_map(path,old,new)[ln]
    assert len(nls)==1, (name,path,ln,nls)
    assert lines(new,path)[nls[0]-1]==lines(old,path)[ln-1]
    new_decl[name]={'module':src['module'],'file':path,'line':nls[0]}
steps=[]
for x in prev['lean_source_steps']:
    path=x['path']; ln=x['line']; decl=x['declaration_line']; mp=line_map(path, old,new)
    assert len(mp[ln])==len(mp[decl])==1,(x,mp[ln],mp[decl]); l=mp[ln][0]; d=mp[decl][0]
    steps.append({'file':path,'line':l,'declaration_line':d,'identifier':x['identifier'],'line_sha256':hashlib.sha256(lines(new,path)[l-1].encode()).hexdigest()})
numbered={}
for c in claims:
    label=c['label']; key='* '+label+'.'; positions=[t for t,s in enumerate(readings,1) if s.startswith(key)]; assert len(positions)==1,label
    assert label in meta['numbered']; numbered[label]={**c,'reconstruction_line':positions[0],'declarations':meta['numbered'][label]}
num={i+1:c['label'] for i,c in enumerate(claims)}
refs={n:c['label'] for c in claims for n in [c['label']]}
focus=[('sections/01-introduction.tex',193,220,'intro-section-range'),('sections/05a-internal-syntax.tex',285,344,'selector'),('sections/08b-uniform-independent-sentences.tex',1,111,'effective-extensibility'),('sections/04-miller-sequences.tex',28,52,'miller-existence'),('appendices/a-syntax-and-theories.tex',527,588,'regular-image'),('appendices/c-section-lifting.tex',67,205,'oracle-quantifiers'),('appendices/e-reading-lean-proofs.tex',6,240,'appendix-e')]
for f in get('tex-inventory.json')['recursive_order']:
    fp=f['file']; tx='manuscript/latex/'+fp; assert hashlib.sha256(blob(new,tx)).hexdigest()==f['sha256']
allpass=json.loads(gzip.decompress((out/'passages.json.gz').read_bytes())); passages=[]; empty=[]
for p in allpass:
    f=p['file']; a=p['start']; b=p['end']; tx='manuscript/latex/'+f; body='\n'.join(lines(new,tx)[a-1:b]); enclosing=[c['label'] for c in claims if c['file']==f and a<=c.get('proof_end',c['end']) and b>=c['start']]; mentioned=sorted(set(t for t in re.findall(r'\\(?:ref|eqref)\{([^}]+)\}',body) if t in refs)); pf=[name for src,l,h,name in focus if src==f and a<=h and b>=l]; cc=[(x['line'],x['key']) for x in citations if x['file']==f and a<=x['line']<=b]; op=line_map(tx,new,old); oldlines={i for j in range(a,b+1) for i in op.get(j,[])}; older=[q for q in prev['paragraphs'] if q['source']==f and any(q['lines'][0]<=i<=q['lines'][1] for i in oldlines)]
    candidates=sorted({i for q in older for i in q.get('source_steps',[])}); related=sorted({num[i] for q in older for i in q.get('argument_results',[]) if i in num}); oldroles=sorted({q['role'] for q in older})
    arole='statement or proof' if enclosing else 'mathematical exposition'
    if f in ['main.tex','preamble.tex']: arole='entry point, structure or notation'
    if f=='bibliography.tex': arole='bibliography'
    if re.fullmatch(r'(?:\s*(?:\\(?:section|subsection|subsubsection|paragraph)(?:\*)?\{[^\n]+|\\label\{[^}]+\}|\\(?:input|end|begin)\{[^}]+\}|%[^\n]*))+\s*',body): arole='structural or title'
    if arole=='mathematical exposition' and cc and not enclosing and not candidates and not related and not mentioned: arole='literature'
    v={'source':f,'lines':[a,b],'kind':arole,'encloses_or_continues':enclosing,'references':mentioned,'proof_context':related,'step_ids':candidates,'citations':cc,'focus':pf}; passages.append(v)
    if arole=='mathematical exposition' and not any([enclosing,mentioned,pf,cc,candidates,related]): empty.append(v)
assert not empty,empty
full={'commit':new,'reading':'reconstruction.md','explanation':'The exact TeX block digest is in passages.json.gz. An enclosing claim gives its statement, proof and declarations below. Citations are judged individually in sources.json.gz. proof_context and step IDs index the surrounding argument; editorial blocks can inherit context. The changed proof steps named in focus are compared directly in focused-comparisons.md. Step IDs are one-based. Identical Lean source lines were reidentified at the tested revision.','numbered':numbered,'declarations':new_decl,'lean_steps':steps,'passages':passages}; gz('correspondence.json.gz',full)
tag=subprocess.check_output(['git','rev-parse','cei-v72-palomar-v3^{commit}'],cwd=root,text=True).strip(); anchor=[]; ep='manuscript/latex/appendices/e-reading-lean-proofs.tex'
for ix,row in enumerate(lines(new,ep),1):
    for m in re.finditer(r'\\CEIproof\{([^}]+)\}\{L(\d+)-L(\d+)\}\{([^}]+)\}',row):
        f='Lean/'+m[1]+'.lean'; x,y=map(int,m.group(2,3)); original=lines(tag,f)[x-1:y]; current=lines(new,f)[x-1:y]; assert len(original)==y-x+1; assert original==current,(f,x,y); anchor.append({'tex_line':ix,'file':f,'start':x,'end':y,'description':m[4],'text_sha256':hashlib.sha256('\n'.join(original).encode()).hexdigest()})
assert len(anchor)==20; (out/'appendix-e-links.json').write_text(json.dumps({'commit':new,'registered_commit':tag,'links':anchor},indent=1)+'\n')
print(len(numbered),len(passages),len(new_decl),len(steps),len(anchor))
# Preserve a finer index into paragraphs containing several formulas and assertions.
# Use offsets as well as line numbers so adjacent sentences sharing a line remain distinguishable.
ledger=lines(new,'FORMALIZATION_STATUS_V93.md'); anchors={}
for ln,row in enumerate(ledger,1):
    for f,d in re.findall(r'\]\(manuscript/latex/([^()#]+)#L(\d+)\)',row):
        anchors.setdefault(f,[]).append((int(d),ln))
segments=[];outline=[];seen=set();sec=0;sub=0;app=False
for idx,p in enumerate(passages,1):
    f=p['source'];a,b=p['lines']; seq=lines(new,'manuscript/latex/'+f)[a-1:b];body='\n'.join(seq)
    for i,ln in enumerate(seq,a):
        if f=='main.tex' and ln.strip()==r'\appendix':app=True;sec=0
        main=re.search(r'^\\(section|subsection)\{',ln)
        if main:
            if main[1]=='section': sec+=1;sub=0
            else: sub+=1
            code=chr(64+sec) if app else str(sec)
            if main[1]=='subsection':code+='.'+str(sub)
            heading=ln[main.end():].split('\\label{')[0].strip().removesuffix('}')
            outline.append({'section':code,'source':f,'line':i,'heading_tex':heading})
    bounds={0,len(body)}
    for m in re.finditer(r'(?<=[.!?])\s+(?=(?:[A-Z]|\$|\\(?:begin|end|emph|text|cite|\[)))|(?=\\\[|\\begin\{(?:align\*?|equation\*?|gather\*?|tikzcd)\})|(?<=\\\])|(?<=\\end\{align\})|(?<=\\end\{equation\})',body):bounds.add(m.start());bounds.add(m.end())
    cuts=sorted(bounds)
    for x,y in zip(cuts,cuts[1:]):
        while x<y and body[x].isspace():x+=1
        while y>x and body[y-1].isspace():y-=1
        if x==y: continue
        first=a+body.count('\n',0,x);last=a+body.count('\n',0,y-1); ll=[no for off,no in anchors.get(f,[]) if first<=off<=last]
        segments.append({'block':idx,'offsets':[x,y],'lines':[first,last],'sha256':hashlib.sha256(body[x:y].encode()).hexdigest(),'direct_ledger_lines':ll})
assert len(segments)>len(passages)
gz('sentence-and-display-index.json.gz',{'commit':new,'units':'Nonempty text fragments split at sentence and display boundaries. Offsets are zero-based characters in the block from the sealed passage inventory, including embedded newline characters. Each block has its full mathematical context, citations, labels and Lean step pointers in correspondence.json.gz. Some long displays span several proof inferences.','segments':segments,'outline':outline});print(len(segments),len(outline))
