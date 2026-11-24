# First reader’s evidence for manuscript v81

The first-reader source and correspondence commit is `830d03a5adcf144a003feb36f88bd06e0c5b0cf5`. The independent reconstruction, source verdict and reconciliation have separate SHA-256 manifests. The publication list names the evidence files. The 25 TeX inputs are already in the tested Git object. The original authors’ publications are linked in the reports. [Publication files](publication-files.json) · [Blind seal](blind.sha256) · [Source-verdict seal](source-verdict.sha256) · [Reconciliation seal](reconciliation.sha256)

## Replaying the source evidence

Use a checkout of the tested revision with its pinned Lean environment. Copy the files in this first-reader directory into a fresh scratch directory in that checkout. Copy the tree of `.tex` files from `manuscript/latex` into `paper` in the scratch directory, preserving subdirectories. For example, from the scratch directory the following command restores the exact 25 inputs even when the current manuscript on another branch has changed.

```sh
python3 - <<'PY'
import json
from pathlib import Path
import subprocess

revision = '830d03a5adcf144a003feb36f88bd06e0c5b0cf5'
manifest = json.loads(subprocess.check_output(['git', 'show', revision + ':MANUSCRIPT_CURRENT.json']))
for entry in manifest['files']:
    name = entry['path']
    if name.endswith('.tex'):
        dest = Path('paper') / Path(name).relative_to('manuscript/latex')
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_bytes(subprocess.check_output(['git', 'show', revision + ':' + name]))
PY
sha256sum -c paper-inputs.sha256
sha256sum -c blind.sha256
sha256sum -c source-verdict.sha256
sha256sum -c reconciliation.sha256
```

Run `python3 inventory.py` to rebuild the lossless reading inventory, `python3 compare.py` to regenerate the 25 input comparisons and the 80-row declaration index, `python3 index-passages.py` to rebuild the passage crosswalk, and `python3 proof-links.py` to compare Appendix E with the existing `cei-v72-palomar-v3` tag. These generators write to their own scratch directory. Recheck the blind and source-verdict seals after regeneration. The generated crosswalk characterizes candidate declaration names. The actual types and transitive axioms are in the independent Lean transcripts. [Numbered declarations](numbered-sources.jsonl) · [Lean input](numbered-kernel.lean) · [Lean output](numbered-kernel.log)

Use the repository's prepared, built Lake environment to invoke Lean from the tested checkout’s `Lean` directory. Set `audit_dir` to the absolute path of the first-reader scratch copy. Run the following commands in sequence. The original third run used `run-independent.py` to supply any missing compiled modules from the tested sources in a scratch overlay. Its imported-module paths and the reported Lean version are specific to the pinned revision.

```sh
lake env lean --memory=5000 --threads=1 "$audit_dir/expected.lean"
lake env lean --memory=5000 --threads=1 "$audit_dir/numbered-kernel.lean" > "$audit_dir/replayed-numbered.log"
lake env lean --memory=5000 --threads=1 "$audit_dir/independent-applications.lean" > "$audit_dir/replayed-applications.log"
cmp "$audit_dir/numbered-kernel.log" "$audit_dir/replayed-numbered.log"
cmp "$audit_dir/independent-applications.log" "$audit_dir/replayed-applications.log"
```

## Checking the official wrapper

`confirm-receipt.py` verifies the full original wrapper JSON, both of its axiom transcripts, its strict-module transcripts, the Git source snapshot and all 844 independently queried declarations. It compares each strict-only statement alias with the transcript that actually prints its axioms. Given the original run directory and the consolidated gzip, the following invocation also verifies that the parsed `verification` agrees and that `official_json_sha256` is the digest of the original unmodified bytes. The wrapper records wall-clock timings, so its raw digest identifies that particular run. [Receipt-comparison program](confirm-receipt.py) · [Consolidated kernel receipt](../../../../V81_WSL2_LEAN_VERIFICATION.json.gz)

```sh
python3 confirm-receipt.py --run "$original_run" --packed "$published_gzip" --out checked-receipt.json
```
