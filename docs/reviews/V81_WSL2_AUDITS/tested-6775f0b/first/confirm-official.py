#!/usr/bin/env python3
"""Check the full WSL kernel receipt for the exact version 81 source revision."""
import argparse
import gzip
import hashlib
import json
import subprocess
from pathlib import Path

TESTED = '6775f0b3a5fb668f9390b21440f3f6c57bc65930'
ALLOWED = {'Classical.choice', 'propext', 'Quot.sound'}

def require(condition, reason):
    if not condition:
        raise ValueError(reason)

def verify(path, root, tested):
    raw = json.loads(gzip.decompress(path.read_bytes()))
    require(raw.get('source_commit') == tested,
            f"receipt concerns {raw.get('source_commit')}, expected {tested}")
    require(raw.get('manuscript_version') == 81, 'expected manuscript 81')
    result = raw.get('verification', {})
    require(result.get('success') is True and result.get('scope') == 'full',
            'expected successful full verification')
    wrapper = raw.get('wrapper', {})
    require(wrapper.get('source') == tested and wrapper.get('exit_code') == 0 and
            wrapper.get('argv') == ['bash', 'scripts/verify-wsl.sh'], 'wrapper evidence')
    commands = result['commands']
    require(commands and all(c['exit_code'] == 0 for c in commands), 'exit codes')
    logs = raw['command_log_sha256']
    require(set(logs) == {c['log'] for c in commands} and
            all(len(h) == 64 for h in logs.values()), 'per-command log digests')
    require(set(result['allowed_axioms']) == ALLOWED, 'allowed axiom set')
    for key in ['axioms', 'current_axioms']:
        require(result[key] and all(isinstance(v, list) and set(v) <= ALLOWED
                                   for v in result[key].values()), key)
    require(result['current_audit_modules'], 'empty production module audit')
    for module in result['current_audit_modules']:
        name = module.replace('.', '/') + '.lean'
        require(any(name in c['argv'] for c in commands), f'missing strict source replay for {module}')
    m = result['current_manuscript']
    require(m['version'] == 81 and m['pdf_copy_matches'] and m['source_archive_matches'],
            'active manuscript artifacts')
    require(not result['source_mismatches'], 'unexpected source mismatches')
    deps = result['dependency_worktrees']
    require(deps['end'] == deps['start'] == result['dependencies'] and
            all(d['worktree_clean'] and d['expected'] == d['actual'] for d in deps['end']),
            'dependency provenance')
    official = hashlib.sha256((json.dumps(result, indent=2) + '\n').encode()).hexdigest()
    require(official == raw['official_json_sha256'], 'original verifier receipt digest')
    tree = subprocess.check_output(['git', '-C', str(root), 'ls-tree', '-rz', tested])
    blobs = {}
    for entry in tree.rstrip(b'\0').split(b'\0'):
        attrs, name = entry.split(b'\t', 1)
        blobs[name.decode()] = attrs.split()[2].decode()
    verified = raw['verified_commit_git_blobs']
    require(verified and set(verified) == set(result['integration_sha256']) and
            all(blobs.get(path) == h for path, h in verified.items()), 'tested git blobs')
    require(set(m['sha256']).issubset(verified), 'manuscript files in tested snapshot')
    print(json.dumps({'source_commit': tested, 'manuscript_version': 81,
                      'full_commands': len(commands), 'production_modules': len(result['current_audit_modules']),
                      'production_declarations': len(result['current_axioms']),
                      'retained_declarations': len(result['axioms']), 'git_blobs': len(verified),
                      'receipt_sha256': hashlib.sha256(path.read_bytes()).hexdigest()}))

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('receipt', type=Path)
    parser.add_argument('tested_git_repository', type=Path)
    parser.add_argument('--expected', default=TESTED,
                        help='use a different historical commit as a positive control')
    args = parser.parse_args()
    try:
        verify(args.receipt, args.tested_git_repository, args.expected)
    except (KeyError, ValueError, OSError, subprocess.CalledProcessError) as error:
        parser.exit(1, f'No full receipt certified: {error}\n')
