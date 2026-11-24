"""Check the full wrapper, inputs, dependency pins, commands and individual axiom lists."""
from pathlib import Path
import argparse,gzip,hashlib,json,subprocess,sys
commit='6775f0b3a5fb668f9390b21440f3f6c57bc65930'
pa=argparse.ArgumentParser()
pa.add_argument('--checkout',required=True,type=Path)
pa.add_argument('--receipt',required=True,type=Path)
pa.add_argument('--out',type=Path)
ar=pa.parse_args()
def must(b,m):
 if not b:raise ValueError(m)
try:
 root=ar.checkout.resolve(); rec=ar.receipt.resolve()
 raw=rec.read_bytes(); document=json.loads(gzip.decompress(raw) if raw[:2]==b'\x1f\x8b' else raw)
 must(document.get('source_commit')==commit,'receipt does not identify the tested source commit')
 wrap=document['wrapper'];must(wrap.get('source',commit)==commit and wrap['exit_code']==0,'wrapper failed or source differs')
 must(wrap['argv'][-1]=='scripts/verify-wsl.sh','wrapper path')
 v=document['verification'];must(v['success'] is True and v['scope']=='full','full replay incomplete')
 cmd=v['commands'];must(cmd and all(c['exit_code']==0 for c in cmd),'failed verifier command')
 must('current-axiom-audit.log' in {Path(c['log']).name for c in cmd},'current axiom command')
 must('axiom-audit.log' in {Path(c['log']).name for c in cmd},'retained axiom command')
 m=v['current_manuscript'];must(m['version']==81 and m['source_archive_matches'] and m['pdf_copy_matches'],'manuscript assets')
 must(not v['source_mismatches'],'verifier provenance mismatches')
 allowed={'propext','Classical.choice','Quot.sound'}
 must(set(v['allowed_axioms'])==allowed,'unexpected verifier axiom policy')
 for group in ['axioms','current_axioms']:
  must(v[group] and all(set(axioms)<=allowed for axioms in v[group].values()),'unexpected or missing axiom list')
 deps=v['dependency_worktrees'];must(deps['start']==deps['end'] and deps['start'],'dependency state drift')
 must(all(x['worktree_clean'] and x['actual']==x['expected'] for x in deps['start']),'unverified dependency')
 snapshot=v['integration_sha256']
 must(snapshot and all(snapshot.get(k)==val for k,val in m['sha256'].items()),'manuscript SHA-256 differs')
 digest=lambda b: hashlib.sha256(b).hexdigest()
 must(digest(json.dumps(snapshot,sort_keys=True).encode())==v['source_snapshot_sha256'],'snapshot digest')
 if document.get('official_json_sha256'):
  must(digest((json.dumps(v,indent=2)+'\n').encode())==document['official_json_sha256'],'official JSON digest')
 if document.get('command_log_sha256'):
  must({c['log'] for c in cmd}==set(document['command_log_sha256']),'command log receipt coverage')
 # Hash the committed bytes of every measured path with one sequential Git batch.
 proc=subprocess.Popen(['git','cat-file','--batch'],cwd=root,stdin=subprocess.PIPE,stdout=subprocess.PIPE)
 for path,expected in sorted(snapshot.items()):
  if '\n' in path:raise ValueError('invalid snapshot path')
  proc.stdin.write((commit+':'+path+'\n').encode());proc.stdin.flush();head=proc.stdout.readline().split()
  must(len(head)==3 and head[1]==b'blob','absent Git blob '+path)
  data=proc.stdout.read(int(head[2]));must(proc.stdout.read(1)==b'\n','invalid Git batch terminator')
  must(digest(data)==expected,'committed data digest differs for '+path)
 proc.stdin.close();must(proc.wait()==0,'Git batch failed')
 result=dict(status='pass',source_commit=commit,manuscript_version=m['version'],receipt_sha256=digest(raw),
             zero_exit_commands=len(cmd),verified_input_blobs=len(snapshot),clean_pinned_dependencies=len(deps['start']),
             current_axioms=len(v['current_axioms']),retained_axioms=len(v['axioms']),permitted_axioms=sorted(allowed))
except (KeyError,AssertionError,ValueError,OSError) as e:
 print('FAIL:',str(e),file=sys.stderr);sys.exit(1)
s=json.dumps(result,indent=2)+'\n'
if ar.out:ar.out.write_text(s)
print(s,end='')
