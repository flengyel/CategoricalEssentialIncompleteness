from pathlib import Path
import re, json, hashlib

BASE = Path('output/manuscript/local_connectedness')
OUT = Path('tmp/scope26')
OUT.mkdir(exist_ok=True)

flat=[]
def expand(path):
    for n,line in enumerate(path.read_text().splitlines(),1):
        inc=re.fullmatch(r'\s*\\input\{([^}]+)\}\s*',line)
        if inc:
            name=inc.group(1)
            if not Path(name).suffix:name+='.tex'
            expand(BASE/name)
        else:flat.append((str(path.relative_to(BASE)),n,line))
expand(BASE/'main.tex')
text='\n'.join(x[2] for x in flat)+'\n'
starts=[];pos=0
for f,n,line in flat:starts.append(pos);pos+=len(line)+1
import bisect
def loc(pos):
    i=bisect.bisect_right(starts,pos)-1
    f,n,_=flat[i];return {'file':f,'line':n}
aux=(BASE/'main.aux').read_text()
auxlabels={m.group(1):{'number':m.group(2),'page':int(m.group(3))}
           for m in re.finditer(r'\\newlabel\{([^}]+)\}\{\{([^}]*)\}\{(\d+)\}',aux)}
toc_pages={}
for line in aux.splitlines():
    ident=re.search(r'\\numberline\s*\{([^}]+)\}',line)
    page=re.search(r'\}\{(\d+)\}\{(?:section|subsection|appendix)\.',line)
    if ident and page:toc_pages[ident.group(1)]=int(page.group(1))
def braced(start):
    depth=0
    for i in range(start,len(text)):
        if text[i]=='{':depth+=1
        elif text[i]=='}':
            depth-=1
            if depth==0:return text[start+1:i],i+1
    raise ValueError('Unterminated heading')
heads=[];sec=0;sub=0;appendix=False
for m in re.finditer(r'\\appendix\b|\\(section|subsection)\{',text):
    if m.group(0).startswith('\\appendix'):
        appendix=True;sec=0;sub=0;continue
    kind=m.group(1);title,title_end=braced(m.end()-1)
    if kind=='section':sec+=1;sub=0
    else:sub+=1
    ident=(chr(64+sec) if appendix else str(sec))+('' if kind=='section' else '.'+str(sub))
    heads.append({'id':ident,'kind':kind,'title':title,'start':m.start(),
                  'page':toc_pages.get(ident),**loc(m.start())})
    # A heading's label is normally immediately after it.
    nxt=text[title_end:title_end+180]
    lm=re.match(r'\s*\\label\{([^}]+)\}',nxt)
    if lm and lm.group(1) in auxlabels:heads[-1].update(auxlabels[lm.group(1)])
def heading(pos):
    prior=[h for h in heads if h['start']<=pos]
    return prior[-1] if prior else {'id':'front','title':'Front matter'}
results=[]
for m in re.finditer(r'\\begin\{(theorem|proposition|lemma|corollary|definition)\}(?:\[([^\]]*)\])?',text):
    kind,title=m.group(1),m.group(2) or ''
    endtag='\\end{'+kind+'}'
    end=text.index(endtag,m.end())+len(endtag)
    proof=re.match(r'\s*\\begin\{proof\}',text[end:])
    proofend=end
    if proof:proofend=text.index('\\end{proof}',end+proof.end())+len('\\end{proof}')
    statement=text[m.end():end-len(endtag)]
    labels=re.findall(r'\\label\{([^}]+)\}',statement)
    primary=next((x for x in labels if x in auxlabels),labels[0] if labels else '')
    meta=auxlabels.get(primary,{})
    results.append({'kind':kind,'title':title,'label':primary,'aliases':labels,
        'number':meta.get('number',''),'page':meta.get('page'),
        'section':heading(m.start())['id'],'heading':heading(m.start())['title'],
        'start':m.start(),'end':proofend,'statement':statement.strip(),
        **loc(m.start()),'end_location':loc(proofend-1)})
all_labels=[]
for m in re.finditer(r'\\label\{([^}]+)\}',text):
    owner=next((r for r in results if r['start']<=m.start()<r['end']),None)
    all_labels.append({'label':m.group(1),'position':m.start(),
        'owner':owner['label'] if owner else None,
        'section':heading(m.start())['id'],**loc(m.start()),**auxlabels.get(m.group(1),{})})
labelmap={x['label']:x for x in all_labels}
refs=[]
for m in re.finditer(r'\\(?:eqref|ref|autoref|[Cc]ref)\{([^}]+)\}',text):
    owner=next((r for r in results if r['start']<=m.start()<r['end']),None)
    for label in m.group(1).split(','):
        refs.append({'target':label,'source_result':owner['label'] if owner else None,
            'source_section':heading(m.start())['id'],**loc(m.start())})
for r in results:
    r['explicit_reference_labels']=sorted(set(x['target'] for x in refs if x['source_result']==r['label']))
    r['explicit_result_dependencies']=sorted(set(labelmap[x]['owner'] for x in r['explicit_reference_labels']
        if x in labelmap and labelmap[x]['owner'] and labelmap[x]['owner']!=r['label']))
    r['incoming_reference_locations']=[x for x in refs if x['target'] in r['aliases']]
    r['incoming_result_references']=sorted(set(x['source_result'] for x in r['incoming_reference_locations']
        if x['source_result'] and x['source_result']!=r['label']))
data={'baseline_commit':'490418a5eecbefa532e4d9283a7d504e4c611198',
      'source_sha256':hashlib.sha256(text.encode()).hexdigest(),
      'headings':heads,'results':results,'labels':all_labels,'references':refs,
      'note':'Explicit references are a navigation index, not a complete semantic proof-dependency graph.'}
(OUT/'inventory.json').write_text(json.dumps(data,ensure_ascii=False,indent=2)+'\n')
(OUT/'expanded_source.tex').write_text(text)
for h in heads:print(h['id'],h['title'],h.get('page',''),h['file']+':'+str(h['line']))
print('RESULTS',len(results),'LABELS',len(all_labels),'REFERENCES',len(refs))
for r in results:
    print(r['kind'],r['number'],r['label'],str(r['page']),r['section'],
          'deps='+','.join(r['explicit_result_dependencies']))
