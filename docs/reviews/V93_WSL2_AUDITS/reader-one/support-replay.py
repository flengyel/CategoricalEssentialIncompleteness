"""Replay the specialized application inputs and inspect the constants in selected proof terms."""
import ast, datetime, gzip, hashlib, io, json, os, subprocess, sys, tarfile
from pathlib import Path
art=Path(__file__).resolve().parent
pin=Path(sys.argv[1]).resolve(); out=Path(sys.argv[2]).resolve(); out.mkdir(parents=True,exist_ok=True)
sha='2269c9674e710a7032e6751e7db2473147aaaf96'; assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=pin,text=True).strip()==sha
name=lambda t: datetime.datetime.now(datetime.timezone.utc).isoformat();H=lambda b:hashlib.sha256(b).hexdigest()
chart={}; args=['lake','env','lean','-DwarningAsError=true','--stdin']; env={**os.environ,'LEAN_NUM_THREADS':'1'}
def run(title,data):
  start=name(0); p=subprocess.run(args,cwd=pin/'Lean',env=env,input=data,stdout=subprocess.PIPE,stderr=subprocess.STDOUT); (out/(title+'.lean')).write_bytes(data);(out/(title+'.log')).write_bytes(p.stdout)
  chart[title]={'start_utc':start,'end_utc':name(0),'input_sha256':H(data),'output_sha256':H(p.stdout),'exit':p.returncode};print(title,p.returncode,flush=True)
  if p.returncode: raise SystemExit(out/(title+'.log'))
  return p.stdout.decode()
local='CategoricalEssentialIncompleteness.'; lc=local+'LocalConnectedness.';v46=local+'V46.'
imports=['ArithmeticInseparability','CountableArithmeticModels','V46MillerCanonicalAxiomIncompleteness','V46MillerFixedPoint','V46MillerTheoryDomainApplication','V46UltrapowerComparisonChecks','V46OracleMachineDomains','V46AssociatedClosedTheories','V46SelectorGraph','V46RegularImage','V46DominicalDiagonal','V46ArithmeticUniformIndependent']; ns={local+'ArithmeticSyntax.':['supports_recursivelyInseparable_of_definability','supports_recursivelyInseparable'],local+'ArithmeticRepresentation.':['StrongNumeralwise','consistent_not_both'],lc+'SyntacticModel.':['exists_nat_elementary','complete_nat_models','modelIndex_nonempty','joint_faithful_nat'],v46+'Miller.CanonicalAxiomIncompleteness.':['recoveredCodes_enumerable','axiom_subobject_recovery','sentence_image_recovery','printed_essential_incompleteness_of_consistent','printed_native_incomplete_of_consistent'],v46+'Miller.TheoryDomainApplication.':['theorem_mem'],v46+'Miller.':['exists_coordinate_fixedPoint','exists_isMiller'],v46+'ArithmeticUltrapower.Checks.':['unary_predicate','graph_value','pa_axiom'],lc+'OracleComputation.':['machine_section','exists_prefix_compiler'],v46+'FiniteSigmaOne.':['selected_entries_PA','selected_entries_model'],lc+'V46.':['range_regularImage'],v46+'DominicalDiagonal.':['zero_of_empty_preimages','fixed_source_diagonal'], 'CategoryTheory.IsSection.':['isRange']}
header=next(ast.literal_eval(n.value) for n in ast.parse((art/'replay.py').read_text()).body if isinstance(n,ast.Assign) and isinstance(n.targets[0],ast.Name) and n.targets[0].id=='header');header=header.replace('  let mod ← findModuleOf? n','  let ci ← getConstInfo n\n  let deps := (ci.value? true).map fun e => e.getUsedConstants.map Name.toString\n  let mod ← findModuleOf? n');header=header.replace('("module",toJson (mod.map Name.toString))','("module",toJson (mod.map Name.toString)),("proof_constants", toJson deps)');names=[p+n for p,ns in ns.items() for n in ns];inp=''.join('import '+local+i+'\n' for i in imports)+header+''.join('#reader_application '+n+'\n' for n in names)
rich=run('Support',inp.encode()); details={}
for l in rich.splitlines():
 if l.startswith('READER:'):
  v=json.loads(l[7:]);n=v.pop('constant');assert v['proof_constants'] and set(v['axioms'])<={'propext','Classical.choice','Quot.sound'},n;details[n]=v
assert list(details)==names
archive='docs/reviews/V84_WSL2_AUDITS/reader-one/proof-inputs.tar.gz'; raw=subprocess.check_output(['git','show',sha+':'+archive],cwd=pin)
with tarfile.open(fileobj=io.BytesIO(raw),mode='r:gz') as tape:
 for member in tape.getmembers():
  if member.name.startswith('Application'):
   run(Path(member.name).stem,tape.extractfile(member).read())
result={'commit':sha,'argv':args,'preexisting_concrete_input_archive':archive,'preexisting_archive_sha256':H(raw),'commands':chart,'supporting_types_and_direct_proof_constants':details};(out/'support.json.gz').write_bytes(gzip.compress(json.dumps(result,ensure_ascii=False,separators=(',',':')).encode(),mtime=0))
