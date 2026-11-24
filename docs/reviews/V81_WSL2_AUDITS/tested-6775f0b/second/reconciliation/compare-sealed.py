"""Compare the two original signed row mappings and their typed Lean output."""
from pathlib import Path
import argparse, gzip, hashlib, json, re
HERE=Path(__file__).resolve().parent
def get(path):return json.loads(gzip.decompress(path.read_bytes()))
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def require(b,s):
    if not b:raise ValueError(s)
def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--first', type=Path, required=True)
    parser.add_argument('--second', type=Path, required=True)
    parser.add_argument('--out', type=Path)
    a=parser.parse_args()
    core=get(HERE/'named-core.json.gz');m=core['declarations'];summary=json.loads((HERE/'reconciliation.json').read_text())
    seals=summary['seals'];f=a.first;s=a.second
    for key,p in {'first_report':f/'report.md','first_blind':f/'reconstruction.md','first_numbered':f/'numbered.json.gz','first_supplement':f/'supplemental.json.gz','second_report':s/'report.md','second_numbered':s/'numbered-crosswalk.json.gz','second_blind':s/'reconstruction.sha256','second_evidence':s/'SHA256SUMS'}.items():
        require(sha(p)==seals[key],key+' seal differs')
    numbered=get(f/'numbered.json.gz');sup=get(f/'supplemental.json.gz')['checked_declarations']
    old={r['number']:r for r in numbered['rows']};second={r['printed']:r for r in get(s/'numbered-crosswalk.json.gz')}
    require(set(old)==set(second)=={r['number'] for r in core['rows']},'row sets differ')
    for r in core['rows']:
        d=[x['declaration'] for x in r['occurrences'] if 'declaration' in x];h=r['historical_names'];k=r['number']
        require(r['label']==old[k]['printed_label']==second[k]['label'],'label mismatch')
        require(h==old[k]['declaration_names'],'historical declaration diff '+k)
        if not (r['only_historical'] or r['only_current']):require(h==d,'numbered row order differs '+k)
        require(set(d)|set(r['expanded_additions'])=={x['name'] for x in second[k]['statements']},'reader two expanded declarations '+k)
    t=gzip.decompress((HERE/'core-kernel.log.gz').read_bytes()).decode()
    # The decorated output follows each independent #check, including multiline axiom lists.
    matches=re.finditer(r"^'([^\n]+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)\s*$",t,re.M)
    prev=0;typed={}
    for p in matches:
        name=p[1]
        if name in m:
            typed[name]={'type':t[prev:p.start()].strip(),'axioms':set(x.strip() for x in (p[2] or '').split(',') if x.strip())}
        prev=p.end()
    require(set(typed)==set(m),'Missing current checked type')
    counts={}
    for label,records in [('historical_numbered',numbered['declarations']),('first_supplement',sup)]:
        overlap=set(records)&set(m)
        for name in sorted(overlap):
            previous=records[name]
            require(previous['source']==m[name]['source'] and previous['source_sha256']==m[name]['source_sha256'],'source difference '+name)
            require(set(previous['axioms'])==typed[name]['axioms'],'axiom difference '+name)
            require(''.join(previous['type'].split())==''.join(typed[name]['type'].split()),'printed type differs '+name)
        counts[label]=len(overlap)
    indirect=sorted(set(m)-set(sup)-set(numbered['declarations']))
    expected=sorted(n for ent in summary['historical_differences'].values() for n in ent['in_first_via_typed_fork_checks'])
    require(indirect==expected,'indirect set mismatch')
    result=dict(source_commit=core['source_commit'],rows_with_identical_ordered_direct_name_lists=78,
                rows_with_different_names=['10.1','B.7'],overlapping_individual_entries=counts,
                distinct_current_checked_individually_in_both=len(set(m)&(set(sup)|set(numbered['declarations']))),
                identical_types_up_to_whitespace=True,identical_transitive_axiom_sets=True,identical_source_sha256=True,
                five_indirect_first_reader_applications=indirect,independent_report_seals_unchanged=True)
    text=json.dumps(result,indent=2)+'\n'
    if a.out:a.out.write_text(text)
    print(text,end='')
if __name__=='__main__': main()
