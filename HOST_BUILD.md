# Hosted build environment

The build uses the official Linux x86-64 Lean 4.35.0-rc2 distribution
(compiler commit `11acb17ec6b07a8f9e9173e6845197929540936b`). The archive is
extracted with `tar --no-same-owner` because this execution host cannot assign
the release archive's original user and group IDs.

The host permits reading `/proc/self/exe` but rejects `/proc/<own-pid>/exe`.
Lean's `IO.appPath` uses the latter spelling, so its unmodified executable
initially reports `failed to locate application`. The small C adapter in
`scripts/host_proc_self_compat.c` retries only that exact self-reference through
`/proc/self/exe` after `ENOENT` or `EACCES`. It does not redirect any other path
or alter Lean's compiler files, elaborator, kernel, source proofs, or objects.

This adapter is specific to the hosted environment; ordinary Linux and WSL 2
builds should use the commands in `README.md` without it. To reproduce the
host adapter when the same executable-path restriction exists:

```bash
cc -shared -fPIC -O2 -Wall -Wextra \
  -o /absolute/build/path/proc_self_compat.so \
  scripts/host_proc_self_compat.c -ldl
LD_PRELOAD=/absolute/build/path/proc_self_compat.so \
  python3 scripts/verify.py
```

The verification script inherits this process-local environment setting. It
retains command exit codes and records all eleven axiom checks. Mathlib objects
come from its standard cache for the pinned source revision. Project sources
and the required Foundation sources are compiled in the combined workspace.
