"""Replay the second reader's probes from the tested repository's Lean directory."""
import gzip
import hashlib
import json
import os
import pathlib
import re
import subprocess
import tempfile

package = pathlib.Path(__file__).resolve().parent
records = json.loads(gzip.decompress((package / 'strict-checks.json.gz').read_bytes()))
checked = subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip()
if checked != records['commit']:
    raise SystemExit(f'Tested commit {records["commit"]} is required, found {checked}')
if not pathlib.Path('lean-toolchain').is_file():
    raise SystemExit('Run from the repository Lean directory')
permitted = {'Classical.choice', 'Quot.sound', 'propext'}
with tempfile.TemporaryDirectory() as temporary:
    for run in records['runs']:
        source = run['input'].encode()
        if hashlib.sha256(source).hexdigest() != run['source_sha256']:
            raise SystemExit(f'Input hash mismatch for {run["file"]}')
        file = pathlib.Path(temporary) / run['file']
        file.write_bytes(source)
        process = subprocess.run(records['command'] + [str(file)], stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT, env={**os.environ, 'LEAN_NUM_THREADS':'1', 'OMP_NUM_THREADS':'1'})
        output = process.stdout.decode()
        observed = re.findall(r"'([^']+)' (?:depends on axioms|does not depend on any axioms)", output)
        used = {name.strip() for names in re.findall(r'depends on axioms:\s*\[([^\]]*)\]', output)
                for name in names.split(',') if name.strip()}
        if (process.returncode or len(observed) != run['requested_axiom_prints'] or
                used - permitted or re.search(r'\b(?:error|warning)(?:\(|:)', output)):
            raise SystemExit(f'{file.name} failed\n{output}')
        print(f'{file.name} passed with {len(observed)} axiom inspections')
