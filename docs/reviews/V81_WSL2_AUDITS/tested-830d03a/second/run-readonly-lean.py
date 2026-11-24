"""Elaborate one review input in scratch using read-only paths to pinned builds."""
import hashlib,json,os,signal,subprocess,sys,time
from pathlib import Path
s=Path(__file__).resolve().parent;p=s.parent/'cei-v81-reviewed'/'Lean';stage=s/'lean-review-stage';stage.mkdir(exist_ok=True)
bin=Path('/home/flengyel/.elan/toolchains/leanprover--lean4---v4.35.0-rc2/bin/lean');name=sys.argv[1];src=s/name
if not src.exists() or src.suffix!='.lean' or src.parent not in {s,s/'numbered-checks'}:raise ValueError(src)
paths=[p/'.lake/build/lib/lean']+sorted(p.glob('.lake/packages/*/.lake/build/lib/lean'))
assert all(x.is_dir() for x in paths)
env={**os.environ,'LEAN_PATH':':'.join(str(x) for x in paths),'LEAN_NUM_THREADS':'1','TMPDIR':str(stage)};out=stage/(src.stem+'.log');meta=stage/(src.stem+'.json');cmd=[str(bin),'-j1','-M1850','-DwarningAsError=true',str(src)];start=time.monotonic();peak=0;stopped=False
with out.open('w') as f:
 proc=subprocess.Popen(cmd,cwd=stage,env=env,stdout=f,stderr=subprocess.STDOUT,start_new_session=True)
 while proc.poll() is None:
  try:
   for ln in Path(f'/proc/{proc.pid}/status').read_text().splitlines():
    if ln.startswith('VmRSS:'):peak=max(peak,int(ln.split()[1]));break
  except FileNotFoundError:pass
  if peak>1980000:
   os.killpg(proc.pid,signal.SIGKILL);stopped=True
  time.sleep(.08)
 code=proc.wait()
d={'file':name,'file_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'commit':'830d03a5adcf144a003feb36f88bd06e0c5b0cf5','lean':'4.35.0-rc2','lean_memory_mb':1850,'warnings_are_errors':True,'rss_cutoff_kib':1980000,'peak_observed_rss_kib':peak,'elapsed_sec':round(time.monotonic()-start,2),'rss_cutoff_triggered':stopped,'status':code,'log_sha256':hashlib.sha256(out.read_bytes()).hexdigest(),'normal_pinned_imports':len(paths),'shared_outputs_written':False}
meta.write_text(json.dumps(d,indent=2)+'\n');print(json.dumps(d));print(out.read_text()[:3000]);sys.exit(code)
