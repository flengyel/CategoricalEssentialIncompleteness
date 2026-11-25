"""Check unchanged mathematical Lean text, the actual reapplications, and printed PDF links."""
import functools, gzip, hashlib, json, re, subprocess, sys, zipfile
from pathlib import Path
from pypdf import PdfReader
pin=Path(sys.argv[1]).resolve(); logs=Path(sys.argv[2]).resolve(); art=Path(__file__).resolve().parent
source='2269c9674e710a7032e6751e7db2473147aaaf96';previous='b37f8908435a4c2991af5b95de4645980ac60a05'
def git(*a):return subprocess.check_output(['git',*a],cwd=pin)
def H(x):return hashlib.sha256(x).hexdigest()
def z(p):return json.load(gzip.open(p,'rt'))
def lean_code(s):
 out=[];i=0;block=0;quote=False
 while i<len(s):
  a=s[i:i+2]
  if block:
   if a=='/-':block+=1;i+=2;continue
   if a=='-/':block-=1;i+=2;continue
   i+=1;continue
  if quote:
   out.append(s[i]);
   if s[i]=='\\' and i+1<len(s):i+=1;out.append(s[i]);i+=1;continue
   if s[i]=='"':quote=False
   i+=1;continue
  if a=='/-':block=1;out.append(' ');i+=2;continue
  if a=='--':
   j=s.find('\n',i);i=len(s) if j<0 else j;continue
  if s[i]=='"':quote=True
  out.append(s[i]);i+=1
 assert not block and not quote
 return re.sub(r'\s+',' ',''.join(out)).strip().encode()
changes={}
for f in git('diff','--name-only',previous,source,'--','Lean').decode().splitlines():
 a=git('show',previous+':'+f);b=git('show',source+':'+f);assert f.endswith('.lean') and lean_code(a.decode())==lean_code(b.decode()),f;changes[f]={'previous_blob_sha256':H(a),'v93_blob_sha256':H(b),'executable_text_sha256':H(lean_code(b.decode()))}
manifest=json.loads(git('show',source+':MANUSCRIPT_CURRENT.json'));assert manifest['version']==93
for item in manifest['files']:
 assert H(git('show',source+':'+item['path']))==item['sha256']
arch=pin/manifest['source_archive'];pdf=pin/manifest['pdf'];pdfdata=pdf.read_bytes(); assert pdfdata==git('show',source+':'+manifest['pdf']); assert pdfdata==(pin/'manuscript/latex/main.pdf').read_bytes(); members=[]
with zipfile.ZipFile(arch) as members_: 
 for n in members_.namelist():
  if n.endswith('/'):continue
  data=members_.read(n);assert data==git('show',source+':manuscript/'+n),n; members.append(n)
links=json.loads((art/'appendix-e-links.json').read_text())['links'];urls={'https://github.com/flengyel/CategoricalEssentialIncompleteness/blob/cei-v72-palomar-v3/'+r['file']+'#L'+str(r['start'])+'-L'+str(r['end']) for r in links};doc=PdfReader(pdf);found={}
for i,p in enumerate(doc.pages,1):
 for annot in p.get('/Annots',[]):
  u=annot.get_object().get('/A',{}).get('/URI','')
  if '/cei-v72-palomar-v3/Lean/' in u:found[u]=i
assert set(found)==urls
reference=json.loads(gzip.decompress(git('show',source+':docs/reviews/V84_WSL2_AUDITS/reader-one/applied-types.json.gz')))['claims'];fresh=z(logs/'applied-types.json.gz')['claims'];typematch=0
for name,r in reference.items():
 s=fresh[name];assert r['applied']['conclusion']==s['result'] and r['applied']['parameters']==s['binders'] and r['module']==s['module'] and set(r['axioms'])==set(s['axioms']),name;typematch+=1
supp=z(logs/'support.json.gz'); proofs=supp['supporting_types_and_direct_proof_constants'];names=set(fresh)|set(proofs)
assert all(set(v['axioms'])<={'propext','Classical.choice','Quot.sound'} for v in [*fresh.values(),*proofs.values()]); receipts=z(logs/'commands.json.gz')['commands'];assert all(v['exit']==0 for v in [*receipts.values(),*supp['commands'].values()]);sz=z(art/'sources.json.gz')['works']; assert all(n in names for s in sz.values() for n in s['corresponding_declarations']);c=z(art/'correspondence.json.gz');assert all(n in names for v in c['numbered'].values() for n in v['declarations'])
res={'commit':source,'reference_commit':previous,'changed_Lean_files':changes,'clean_reapplied_reference_types_and_binders_axioms_modules':typematch,'applications':len(fresh),'individual_support_proof_terms_and_types':len(proofs),'distinct_applied_declarations':len(names),'concrete_examples':18,'commands_passing':len(receipts)+len(supp['commands']),'allowed_transitive_axioms':sorted({a for s in [*fresh.values(),*proofs.values()] for a in s['axioms']}),'pdf':manifest['pdf'],'pdf_sha256':H(pdfdata),'pdf_pages':len(doc.pages),'printed_source_links':found,'source_archive':manifest['source_archive'],'archive_bytes_sha256':H(arch.read_bytes()),'archive_member_paths_checked':members,'verified_manifest_files':len(manifest['files'])};(art/'proof-and-artifact-identities.json.gz').write_bytes(gzip.compress(json.dumps(res,ensure_ascii=False,separators=(',',':')).encode(),mtime=0));print({k:v for k,v in res.items() if isinstance(v,int)})
