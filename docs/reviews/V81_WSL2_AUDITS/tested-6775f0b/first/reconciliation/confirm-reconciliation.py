#!/usr/bin/env python3
"""Confirm this adjudication against immutable Git objects and independent Lean output."""
import argparse
import csv
import gzip
import hashlib
import io
import json
import re
import subprocess
import zipfile
from pathlib import Path

TESTED = '6775f0b3a5fb668f9390b21440f3f6c57bc65930'
PRIOR = '98f8d0d50a0cc08885d07ab4d71ec6f6a7adf885'
ALLOWED = {'Classical.choice', 'propext', 'Quot.sound'}
NAME_FIELD = 'named_in_active_cell'
ROOT = Path(__file__).resolve().parent
AXIOM_LINE = re.compile(r"^'([^\n]+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)\s*$", re.M)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def expect(condition, message):
    if not condition:
        raise ValueError(message)

def get_json(path):
    data = Path(path).read_bytes()
    return json.loads(gzip.decompress(data) if data.startswith(b'\x1f\x8b') else data)

def get_blobs(repo, commit, names):
    process = subprocess.Popen(['git', '-C', str(repo), 'cat-file', '--batch'],
                               stdin=subprocess.PIPE, stdout=subprocess.PIPE)
    try:
        for name in sorted(names):
            expect('\n' not in name, 'invalid Git path')
            process.stdin.write((commit + ':' + name + '\n').encode())
            process.stdin.flush()
            header = process.stdout.readline().split()
            expect(len(header) == 3 and header[1] == b'blob', 'missing committed file ' + name)
            body = process.stdout.read(int(header[2]))
            expect(process.stdout.read(1) == b'\n', 'truncated Git object ' + name)
            yield name, header[0].decode(), body
    finally:
        process.stdin.close()
        process.stdout.close()
        expect(process.wait() == 0, 'git cat-file failed')

def local_evidence(repo):
    reg = get_json(ROOT / 'numbered-reconciliation.json.gz')
    named = get_json(ROOT / 'named-probes.json.gz')
    expect(reg['source_commit'] == named['source_commit'] == TESTED, 'local source commit')
    expect(named['number_of_names'] == 1657 and set(named['allowed_axioms']) == ALLOWED and
           named['exit_code'] == 0 and len(named['batches']) == 6, 'detached probe policy and scope')
    expect(len(reg['declarations']) == 1657 and set(named['axioms']) == set(reg['declarations']), 'all declared names')
    all_names = reg['declarations']
    sources = {d['source'] for d in all_names.values()}
    table = reg['numbered_table']
    old_mapping = reg['previous_resolved_reference_file']
    blobs = {p: b for p, _, b in get_blobs(repo, TESTED, sources | {table, old_mapping})}
    expect(sha(blobs[table]) == reg['tested_table_sha256'], 'full correspondence digest')
    expect(sha(blobs[old_mapping]) == reg['previous_resolved_reference_sha256'], 'earlier numbered register')
    target_lines = blobs[table].decode().splitlines()
    _, _, older_table = next(get_blobs(repo, PRIOR, [table]))
    older_lines = older_table.decode().splitlines()
    prior_data = list(csv.DictReader(io.StringIO(blobs[old_mapping].decode()), delimiter='\t'))
    source_lines = {p: b.decode().splitlines() for p,b in blobs.items() if p in sources}
    digests = {p: sha(blobs[p]) for p in sources}
    for name, d in all_names.items():
        expect(d['source_sha256'] == digests[d['source']], 'source digest for ' + name)
        expect(name.rsplit('.',1)[-1] in source_lines[d['source']][d['line']-1], 'source line for ' + name)
        expect(sorted(named['axioms'][name]) == d['axioms'] and set(d['axioms']) <= ALLOWED, 'axioms of ' + name)
    direct = set()
    expanded = set()
    old = set()
    check_rows = {}
    counts = [0,0,0]
    for row in reg['rows']:
        n = row['number']
        raw = target_lines[row['line'] - 1]
        expect(raw == older_lines[row['prior_same_row_line'] - 1] and sha(raw.encode()) == row['row_sha256'], 'row ' + n)
        cell = raw.strip('|').split('|')[2].strip()
        tokens = re.findall(r'`([^`]+)`', cell)
        expect(row['reference_cell'] == cell and row['tokens'] == tokens, 'written references ' + n)
        prior = [r for r in prior_data if r['result'].split()[-1] == n]
        expect([r['printed_reference'] for r in prior] == tokens, 'prior-to-current token mapping ' + n)
        expr = [(r['printed_reference'],r['qualified_name']) for r in prior if r['line_or_reference_kind'].isdigit()]
        mods = [(r['printed_reference'],r['qualified_name']) for r in prior if r['line_or_reference_kind']=='module']
        expect(expr == [(r['token'],r['name']) for r in row['direct']], 'individually named references ' + n)
        expect(mods == [(r['token'],r['module']) for r in row['module_references']], 'module labels ' + n)
        ds = {r[1] for r in expr}
        ep = {q for m in row['module_references'] for q in m['resolved_supporting_names']}
        oldrow = set(row['historical_844_mapping'])
        expect(set(row['expanded_support_beyond_direct']) == ep-ds and
               set(row['expanded_names_already_direct']) == ep&ds, 'resolved module names ' + n)
        expect(set(row['added_since_historical_mapping']) == ds-oldrow and
               set(row['retired_from_historical_mapping']) == oldrow-ds, 'historical row changes ' + n)
        direct.update(ds); expanded.update(ep); old.update(oldrow)
        counts[0] += len(expr); counts[1] += len(mods); counts[2] += len(row['historical_844_mapping'])
        check_rows[n] = (ds, oldrow, ds|ep)
    with gzip.open(ROOT/'active-numbered.tsv.gz','rt',encoding='utf-8',newline='') as active_file:
        only_direct=list(csv.DictReader(active_file,delimiter='\t'))
    expect(len(only_direct)==80,'direct-only table size')
    for saved,r in zip(only_direct,reg['rows'],strict=True):
        expect(saved['printed_number']==r['number'] and saved['tex_label']==r['label'] and
               saved['active_correspondence_line']==str(r['line']) and
               saved['individually_named_references_in_printed_column_order'].split()==[x['name'] for x in r['direct']],
               'direct-only register row '+r['number'])
    expect(len(check_rows)==80 and counts==[855,11,847] and
           [len(direct),len(old),len(direct&old),len(expanded),len(expanded-direct)] == [852,844,836,301,226],
           'row-level counts')
    expect(set(reg['roles'][NAME_FIELD])==direct and set(reg['roles']['direct_or_module_support'])==direct|expanded,
           'role groups')
    seen = set()
    with zipfile.ZipFile(ROOT/'reconciliation-probes.zip') as archive:
        for batch in named['batches']:
            stem = batch['name']; src = archive.read(stem+'.lean'); log = archive.read(stem+'.log')
            run = json.loads(archive.read(stem+'.run.json'))
            expect(batch['exit_code']==run['returncode']==0 and sha(src)==batch['source_sha256']==run['source_sha256']
                   and sha(log)==batch['log_sha256']==run['output_sha256'], 'probe hashes ' + stem)
            requested = re.findall(r'^#check @(\S+)$',src.decode(),re.M)
            expect(requested == re.findall(r'^#print axioms (\S+)$',src.decode(),re.M) and
                   not seen.intersection(requested), 'probe requests ' + stem)
            text=log.decode();cursor=0
            for name, match in zip(requested, AXIOM_LINE.finditer(text), strict=True):
                ax = sorted(v.strip() for v in (match[2] or '').split(',') if v.strip())
                rendered = text[cursor:match.start()].strip()
                expect(name==match[1] and name in rendered.splitlines()[0] and ax==sorted(named['axioms'][name]), 'type or axioms for '+name)
                cursor=match.end()
            expect(not text[cursor:].strip(),'trailing probe material')
            seen.update(requested)
    expect(seen==set(all_names),'full claimed transitive reader coverage')
    return reg,named,check_rows

def validate_receipt(repo, path, reg, named, rows, raw_json, logdir, canonical, require_bound):
    payload = path.read_bytes()
    if canonical:
        expect(canonical.read_bytes()==payload,'canonical and version-specific receipt bytes differ')
    document = get_json(path)
    expect(document.get('source_commit')==TESTED and document.get('manuscript_version')==81, 'different tested source or version')
    v=document.get('verification',{})
    expect(v.get('scope')=='full' and v.get('success') is True, 'expected a completed full replay')
    wrapper=document['wrapper']
    expect(wrapper['source']==TESTED and wrapper['argv']==['bash','scripts/verify-wsl.sh'] and wrapper['exit_code']==0, 'wrapper status')
    expect(document['wrapper_start_status'].strip()=='## HEAD (no branch)' and
           document['wrapper_start_diff_sha256']==sha(b''),'detached clean wrapper start')
    canonical_bytes=(json.dumps(v,indent=2)+'\n').encode()
    expect(sha(canonical_bytes)==document['official_json_sha256'],'official JSON digest')
    if raw_json:
        expect(raw_json.read_bytes()==canonical_bytes,'standalone verifier output')
    expect(v['commands'] and all(e['exit_code']==0 for e in v['commands']),'official exits')
    logs=document['command_log_sha256']
    expect(set(logs)=={x['log'] for x in v['commands']},'command/log coverage')
    required_logs={'current-statement-audit.log','current-axiom-audit.log','axiom-audit.log'}
    expect(required_logs<={Path(n).name for n in logs},'statement and transitive audit commands')
    if logdir:
        for name,h in logs.items():
            expect(sha((logdir / Path(name).name).read_bytes())==h, 'raw command log ' + name)
    strict={q for x in v['commands'] for q in x['argv'] if q.endswith('.lean') and '-DwarningAsError=true' in x['argv']}
    expect(all(m.replace('.','/')+'.lean' in strict for m in v['current_audit_modules']), 'strict production module coverage')
    expect(v['axioms'] and v['current_axioms'] and set(v['allowed_axioms'])==ALLOWED,'axiom audits')
    expect(v['dependency_worktrees']['end']==v['dependency_worktrees']['start']==v['dependencies'] and
           all(d['expected']==d['actual'] and d['worktree_clean'] for d in v['dependencies']),'pins and clean worktrees')
    m=v['current_manuscript']
    measured=v['integration_sha256']
    expect(m['version']==81 and m['tex_files']==25 and m['pdf_copy_matches'] and m['source_archive_matches']
           and all(measured.get(k)==s for k,s in m['sha256'].items()) and not v['source_mismatches'],'manuscript snapshot')
    expect(sha(json.dumps(measured,sort_keys=True).encode())==v['source_snapshot_sha256'],'source snapshot digest')
    ids=document['verified_commit_git_blobs']
    expect(set(ids)==set(measured),'hash schemes cover different inputs')
    for filename,gitid,data in get_blobs(repo,TESTED,measured):
        expect(ids[filename]==gitid and measured[filename]==sha(data),'Git or SHA-256 mismatch '+filename)
    groups={'official_current':v['current_axioms'],'official_retained':v['axioms']}
    if 'supplementary_axioms' in document:
        groups['supplementary_statement_axioms']=document['supplementary_axioms']
    for key in ('current_statement_axioms','statement_axioms'):
        if key in v: groups['official_'+key]=v[key]
        if key in document: groups['reported_'+key]=document[key]
    if 'additional_named_probes' in document:
        extra=document['additional_named_probes']
        expect(extra['source_commit']==TESTED and extra['exit_code']==0,'additional probes source or exit')
        groups['additional_named_probes']=extra['axioms']
    for desc,group in document.get('v81_passage_applications',{}).items():
        groups['passage '+desc]=group
    official_names=set().union(*(set(g) for g in groups.values()))
    seen={}
    for stream,group in groups.items():
        for n,axes in group.items():
            ax=sorted(axes)
            expect(isinstance(axes,list) and set(ax)<=ALLOWED,'unexpected axioms '+n)
            expect(n not in seen or seen[n]==ax,'official maps differ '+n)
            seen[n]=ax
    direct=set(reg['roles'][NAME_FIELD]);all_sources=set(reg['declarations'])
    for n in all_sources & official_names:
        expect(seen[n]==sorted(named['axioms'][n]),'official and detached axiom lists disagree '+n)
    # The canonical wrapper may incorporate the independently compiled checks as an
    # explicit supplement. Bind the entire source and every batch transcript.
    bound=document.get('reader_named_probes')
    if bound is not None:
        expect(bound==named,'bound reader manifest differs from verified local evidence')
    if require_bound:
        expect(bound is not None,'canonical receipt does not embed the reader manifest')
    covered=official_names | (all_sources if bound is not None else set())
    expect(direct<=covered,'direct names not individually reported in this receipt: '+str(sorted(direct-covered)))
    correspondence=document.get('numbered_correspondence',[])
    row_kinds=[]
    if correspondence:
        for row in correspondence:
            n = row.get('number') or row.get('result','').split(' ')[-1]
            refs = row.get('references')
            if refs is None:continue
            names={v['declaration'] for v in refs if not v['module_or_collection']}
            row_kinds.append([n,[key for key,s in zip(('current','historical','including_module_support'), rows[n]) if names==s]])
            expect(row_kinds[-1][1],'unexpected canonical numbered row '+n)
        if row_kinds:expect(len(row_kinds)==80,'incomplete canonical numbered table')
    return dict(full_official_6775=True,receipt_sha256=sha(payload),official_commands=len(v['commands']),
                wrapper_exit=0,production_modules=len(v['current_audit_modules']),measured_git_files=len(ids),
                official_direct_coverage_before_reader_manifest=len(direct&official_names),
                official_all_role_coverage_before_reader_manifest=len(all_sources&official_names),
                bound_reader_manifest=bound is not None,
                official_or_bound_individual_coverage_by_role={k:len(set(s)&covered) for k,s in reg['roles'].items()},
                overlaps_with_official_sources={k:{role:len(set(m)&set(s)) for role,s in reg['roles'].items()}
                                               for k,m in groups.items()},
                official_receipt_names_missing_among_locally_checked=sorted(all_sources-covered),
                canonical_numbered_table_comparison=row_kinds)

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repo',type=Path,required=True)
    p.add_argument('--receipt',type=Path,help='validate a completed official full WSL bundle')
    p.add_argument('--canonical',type=Path,help='also require this receipt to be byte-identical')
    p.add_argument('--raw-verification',type=Path,help='optional original verification.json')
    p.add_argument('--raw-logs',type=Path,help='optional directory holding individual command log files')
    p.add_argument('--require-bound-reader-manifest',action='store_true')
    p.add_argument('--out',type=Path)
    args=p.parse_args();reg,named,rows=local_evidence(args.repo)
    result=dict(signer='Independent first reader',tested_commit=TESTED,
                manuscript_version=81,checked_counts=reg['counts'],full_official_6775=False,
                direct_register_sha256=sha((ROOT/'numbered-reconciliation.json.gz').read_bytes()),
                named_probe_coverage_sha256=sha((ROOT/'named-probes.json.gz').read_bytes()))
    if args.receipt:
        result.update(validate_receipt(args.repo,args.receipt,reg,named,rows,args.raw_verification,args.raw_logs,
                                       args.canonical,args.require_bound_reader_manifest))
    elif args.canonical or args.raw_verification or args.raw_logs or args.require_bound_reader_manifest:
        p.error('supply --receipt for official verification')
    data=json.dumps(result,indent=2)+'\n'
    if args.out:args.out.write_text(data)
    print(data,end='')

if __name__=='__main__':
    try:
        main()
    except (ValueError,KeyError,OSError,subprocess.CalledProcessError) as exc:
        raise SystemExit('No verification for the requested scope: '+str(exc))
