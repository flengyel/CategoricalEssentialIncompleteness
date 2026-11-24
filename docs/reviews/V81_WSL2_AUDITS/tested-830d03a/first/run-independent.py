from pathlib import Path
from hashlib import sha256
import os, re, subprocess, sys, time, json
s=Path(__file__).absolute().parent
root=Path(subprocess.check_output(['git','rev-parse','--show-toplevel'],cwd=s,text=True).strip()); repo=root/'Lean'; base=repo/'.lake/build/lib/lean'; build=s/'stage'; build.mkdir(exist_ok=True)
sha='830d03a5adcf144a003feb36f88bd06e0c5b0cf5'
namespace_build=build/'CategoricalEssentialIncompleteness'
namespace_build.mkdir(exist_ok=True)
for old in (base/'CategoricalEssentialIncompleteness').iterdir():
    dest=namespace_build/old.name
    if old.is_file() and not dest.exists(): dest.symlink_to(old)
base_env=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=repo,text=True).strip()
lean=subprocess.check_output(['elan','which','lean'],cwd=repo,text=True).strip()
env={**os.environ,'LEAN_PATH':str(build)+os.pathsep+base_env}
todo=[]; seen=set()
def add(mod):
    if mod in seen: return
    seen.add(mod)
    relative=Path(*mod.split('.'))
    stale = mod=='CategoricalEssentialIncompleteness.V46OracleSeparatorLift'
    if stale:
        for item in (build/relative.parent).glob(relative.name+'.*'):
            if item.is_symlink(): item.unlink()
    if (not stale and (base/relative.with_suffix('.olean')).is_file()) or (build/relative.with_suffix('.olean')).is_file():return
    src=repo/relative.with_suffix('.lean');
    if not src.is_file():return
    assert subprocess.check_output(['git','show',sha+':Lean/'+str(src.relative_to(repo))],cwd=root)==src.read_bytes()
    for child in re.findall(r'^(?:public |meta |private )*import ([A-Za-z0-9_.]+)',src.read_text(),re.M):add(child)
    todo.append((mod,src,build/relative.with_suffix('.olean')))
for child in re.findall(r'^import ([A-Za-z0-9_.]+)',(s/'independent-applications.lean').read_text(),re.M):add(child)
print('Missing local modules:', [x[0] for x in todo],flush=True)
for mod,src,out in todo:
    out.parent.mkdir(parents=True,exist_ok=True)
    p=subprocess.run([lean,'--memory=5000','--threads=1','-o',str(out),str(src.relative_to(repo))],cwd=repo,env=env,capture_output=True,text=True)
    print(mod,p.returncode,flush=True)
    if p.returncode:
        print(p.stdout,p.stderr,flush=True);sys.exit(p.returncode)
with (s/'independent-applications.log').open('w') as f:
    p=subprocess.run([lean,'--memory=5000','--threads=1',str(s/'independent-applications.lean')],cwd=repo,env=env,stdout=f,stderr=subprocess.STDOUT)
print('applications',p.returncode,flush=True)
sys.exit(p.returncode)
