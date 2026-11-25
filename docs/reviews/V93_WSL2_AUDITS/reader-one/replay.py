"""Check the pinned source, apply each named declaration, and collect its axioms."""
from datetime import datetime, timezone
import gzip, hashlib, io, json, os, subprocess, sys, tarfile
from pathlib import Path

sha='2269c9674e710a7032e6751e7db2473147aaaf96'
art=Path(__file__).resolve().parent
pin=Path(sys.argv[1]).resolve()
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=pin,text=True).strip()==sha
out=Path(sys.argv[2]).resolve(); out.mkdir(parents=True,exist_ok=True)
batches=json.load(gzip.open(art/'query-plan.json.gz','rt'))
permitted={'Classical.choice','propext','Quot.sound'}
header='''import Lean
open Lean Elab Command Meta
set_option pp.maxSteps 2000000
set_option maxRecDepth 4000
elab "#reader_application " d:ident : command => liftTermElabM do
  let n := d.getId
  let c ← mkConstWithFreshMVarLevels n
  let proofType ← inferType c
  let (args,res) ← forallTelescope proofType fun locals goal => do
    let actual ← inferType (mkAppN c locals)
    unless ← isDefEq actual goal do throwError "conclusion failed conversion"
    let args ← locals.mapM fun x => do
      let ld ← x.fvarId!.getDecl
      return Json.mkObj [("binder",toJson ld.userName.toString),
        ("type", toJson (← ppExpr ld.type).pretty)]
    return (args, (← ppExpr goal).pretty)
  let mod ← findModuleOf? n
  let ax ← Lean.collectAxioms n
  logInfo ("READER:" ++ (Json.mkObj [("constant",toJson n.toString),
    ("module",toJson (mod.map Name.toString)),("binders",Json.arr args),
    ("result",toJson res),("axioms",toJson (ax.map Name.toString))]).compress)
'''
def digest(b): return hashlib.sha256(b).hexdigest()
def zwrite(p,d): p.write_bytes(gzip.compress(json.dumps(d,ensure_ascii=False,separators=(',',':')).encode(),mtime=0))
def utc(): return datetime.now(timezone.utc).isoformat()
env=os.environ.copy();env['LEAN_NUM_THREADS']='1'
commands={};results={}
args=['lake','env','lean','-DwarningAsError=true','--stdin']
def run(name,src):
    before=utc()
    done=subprocess.run(args,cwd=pin/'Lean',input=src,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,env=env)
    logfile=out/(name+'.log');logfile.write_bytes(done.stdout)
    (out/(name+'.lean')).write_bytes(src)
    record={'start_utc':before,'end_utc':utc(),'exit':done.returncode,'stdin_sha256':digest(src),'output_sha256':digest(done.stdout)}
    commands[name]=record;zwrite(out/'commands.json.gz',{'commit':sha,'argv':args,'commands':commands})
    print(name,done.returncode,flush=True)
    if done.returncode: raise SystemExit(logfile)
    return done.stdout.decode()
focus=run('Focused',(art/'Focused.lean').read_bytes())
for batch in batches:
    src=''.join('import '+m+'\n' for m in batch['imports'])+header+'\n'+''.join('#reader_application '+n+'\n' for n in batch['declarations'])
    output=run(batch['name'],src.encode())
    names=[]
    for line in output.splitlines():
        if not line.startswith('READER:'): continue
        item=json.loads(line[len('READER:'):]); name=item.pop('constant'); names.append(name)
        assert set(item['axioms'])<=permitted,(name,item['axioms'])
        if name in results: assert results[name]==item,name
        results[name]=item
    assert names==batch['declarations'],(names,batch['name'])
    zwrite(out/'applied-types.json.gz',{'commit':sha,'claims':results})
print('distinct',len(results))
