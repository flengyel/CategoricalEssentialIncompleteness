"""Validate every named reference in the numbered correspondence at the tested commit."""
from pathlib import Path
import argparse, gzip, hashlib, json, os, re, subprocess, tempfile

HERE=Path(__file__).resolve().parent
COMMIT='6775f0b3a5fb668f9390b21440f3f6c57bc65930'
ALLOWED={'propext','Classical.choice','Quot.sound'}
APPLICATIONS={'ReaderTwoNumbered.'+n for n in (
 'both_endpoint_evaluators','total_specialization_at_every_fork','fibres_of_the_specialization')}
def digest(data):
    return hashlib.sha256(data).hexdigest()

def must(test, explanation):
    if not test: raise ValueError(explanation)

def git(root, *args):
    return subprocess.check_output(['git',*args],cwd=root)

def verify_table_and_blobs(root, manifest):
    """Compare the committed markdown, its row tokens and their defining Lean sources."""
    source=manifest['sources']; measured=manifest['declarations']
    md=git(root,'show',COMMIT+':'+source['table_path'])
    must(digest(md)==source['sha256'],'Correspondence hash differs')
    must(git(root,'rev-parse',COMMIT+':'+source['table_path']).decode().strip()==source['git_blob'],'Wrong table blob')
    lines=md.decode().splitlines()
    headings=[(i+1,re.match(r'^\| (?:Theorem|Lemma|Proposition|Corollary|Definition) ([0-9A-E]+\.\d+);',s)) for i,s in enumerate(lines)]
    must([(line,m[1]) for line,m in headings if m]==[(r['line'],r['number']) for r in manifest['rows']],'Number or line mismatch')
    names=[]; collection_count=0; tokens_count=0; by_file={}
    for name,decl in measured.items(): by_file.setdefault(decl['source'],[]).append((name,decl))
    for row in manifest['rows']:
        cells=lines[row['line']-1].strip('|').split('|')
        must(re.search(r'`([^`]+)`',cells[0])[1]==row['label'],'Printed label differs')
        tokens=re.findall(r'`([^`]+)`',cells[2]); tokens_count+=len(tokens)
        must([x['token'] for x in row['occurrences']]==tokens,'Column differs in '+row['number'])
        for x in row['occurrences']:
            if 'collection' in x:
                must(Path(x['source']).stem in {x['token'],'V46'+x['token']},'Collection path mismatch')
                collection_count+=1;continue
            name=x['declaration']; short=x['token']
            if short.startswith('LC.'): short='CategoricalEssentialIncompleteness.LocalConnectedness.'+short[3:]
            elif short.startswith('V46.'):short='CategoricalEssentialIncompleteness.'+short
            must(name==short or name.endswith('.'+short),'Token mismatch '+short)
            names.append(name)
    must(set(names)==set(measured) and (len(manifest['rows']),tokens_count,len(names),len(measured),collection_count,len(by_file))==(80,866,855,852,11,366),'Count or declaration-set mismatch')
    proc=subprocess.Popen(['git','cat-file','--batch'],cwd=root,stdin=subprocess.PIPE,stdout=subprocess.PIPE)
    try:
        for path, entries in sorted(by_file.items()):
            proc.stdin.write((COMMIT+':'+path+'\n').encode());proc.stdin.flush()
            head=proc.stdout.readline().split()
            must(len(head)==3 and head[1]==b'blob','Missing source '+path)
            data=proc.stdout.read(int(head[2]));must(proc.stdout.read(1)==b'\n','Git response')
            fingerprints={entry['source_sha256'] for _,entry in entries}
            must(fingerprints=={digest(data)},'Source hash differs in '+path)
            lean_lines=data.decode().splitlines()
            for name,entry in entries:
                text=lean_lines[entry['line']-1]
                must(re.search(r'\b'+re.escape(entry['kind'])+r'\s+(?:[\w.]+\.)?'+re.escape(name.rsplit('.',1)[-1])+r'(?=\s|\{|\[|:|$)',text) is not None,'No declaration '+name+' at '+path+':'+str(entry['line']))
    finally:
        proc.stdin.close();code=proc.wait()
    must(code==0,'Git cat-file failed')
    return {'rows':80,'backticked_occurrences':tokens_count,'explicit_mentions':len(names),'unique_explicit_names':len(measured),'module_or_collection_references':collection_count,'defining_git_blobs':len(by_file)}

def inspect_output(text, expected):
    ax={n:[x.strip() for x in ls.split(',') if x.strip()] for n,ls in
      re.findall(r"'([^\n]+)' depends on axioms:\s*\[([^\]]*)\]\s*$",text,re.M)}
    ax.update((n,[]) for n in re.findall(r"'([^\n]+)' does not depend on any axioms\s*$",text,re.M))
    must(set(ax)==expected|APPLICATIONS,'Named output differs from the 852 names and three fork applications')
    must(all(set(v)<=ALLOWED for v in ax.values()),'Unexpected proof axiom')
    return {'individual_numbered_axiom_outputs':len(expected),'typed_fork_applications':len(APPLICATIONS),'axioms_used':sorted(set().union(*(set(v) for v in ax.values())))}

def probe_contents(manifest):
    records=manifest['declarations'];modules=sorted({v['module'] for v in records.values()})
    application_text=(HERE/'Applications.lean').read_text()
    imports=''.join('import '+m+'\n' for m in modules)
    proof_commands='\n'.join('#check @'+n+'\n#print axioms '+n for n in sorted(records))
    app_imports, app_body = application_text.split('\n\n',1)
    return imports+app_imports+'\n\nset_option pp.fullNames true\nset_option format.width 150\n\n'+proof_commands+'\n\n'+app_body

def run_lean(root, source, overlay):
    must(git(root,'rev-parse','HEAD').decode().strip()==COMMIT,'Strict replay requires checkout of the tested commit')
    must(not git(root,'diff','--name-only',COMMIT,'--','Lean','scripts','MANUSCRIPT_CURRENT.json','FORMALIZATION_STATUS_V81.md').strip(),'Tracked replay input differs from tested commit')
    lean_root=root/'Lean'
    toolchain=(lean_root/'lean-toolchain').read_text().strip().replace('/','--').replace(':','---')
    binary=Path(os.environ.get('ELAN_HOME',Path.home()/'.elan'))/'toolchains'/toolchain/'bin/lean'
    paths=([overlay.resolve()] if overlay else [])+[lean_root/'.lake/build/lib/lean']+[p/'.lake/build/lib/lean' for p in sorted((lean_root/'.lake/packages').iterdir())]
    with tempfile.TemporaryDirectory(prefix='cei-named-core-') as td:
        p=Path(td)/'CurrentNumbered.lean';p.write_text(source)
        args=[str(binary),'-j1','-DwarningAsError=true','-DautoImplicit=false',str(p)]
        run=subprocess.run(args,cwd=lean_root,env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,paths)),LEAN_NUM_THREADS='1'),stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        if run.returncode:
            print('\n'.join(x for x in run.stdout.decode().splitlines() if 'error' in x)[:4000])
        must(run.returncode==0,'Lean exited '+str(run.returncode))
        return run.stdout,{'argv':[str(binary),'-j1','-DwarningAsError=true','-DautoImplicit=false','CurrentNumbered.lean'],'exit_code':run.returncode,'working_directory':'Lean','lean_version':subprocess.check_output([str(binary),'--version'],text=True).strip(),'read_only_overlay':str(overlay) if overlay else None}

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--checkout',type=Path,required=True)
    ap.add_argument('--manifest',type=Path,default=HERE/'named-core.json.gz')
    opts=ap.add_mutually_exclusive_group()
    opts.add_argument('--run-lean',action='store_true')
    opts.add_argument('--verify-log',type=Path)
    ap.add_argument('--overlay',type=Path,help='Optional directory of already-compiled dependencies')
    ap.add_argument('--save-log',type=Path,help='Write deterministic compressed kernel output')
    ap.add_argument('--result',type=Path)
    args=ap.parse_args();root=args.checkout.resolve()
    manifest=json.loads(gzip.decompress(args.manifest.read_bytes()));must(manifest['source_commit']==COMMIT,'Wrong manifest commit')
    report={'tested_commit':COMMIT,'manifest_sha256':digest(args.manifest.read_bytes())}|verify_table_and_blobs(root,manifest)
    source=probe_contents(manifest);report['generated_lean_source_sha256']=digest(source.encode())
    if args.run_lean:
        raw,receipt=run_lean(root,source,args.overlay);report.update(receipt)
        if args.save_log:args.save_log.write_bytes(gzip.compress(raw,mtime=0))
    elif args.verify_log:
        data=args.verify_log.read_bytes();raw=gzip.decompress(data) if data[:2]==b'\x1f\x8b' else data
    if args.run_lean or args.verify_log:
        report.update(inspect_output(raw.decode(),set(manifest['declarations'])));report['uncompressed_lean_log_sha256']=digest(raw)
    out=json.dumps(report,indent=2)+'\n'
    if args.result:args.result.write_text(out)
    print(out,end='')

if __name__=='__main__':main()
