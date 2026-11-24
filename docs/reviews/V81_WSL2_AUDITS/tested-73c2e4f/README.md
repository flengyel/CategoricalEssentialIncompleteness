# Targeted v81 verification at 73c2e4f

The clean worktree at `73c2e4fa2bc633a3af012b1c4f85a7882018f962` passed all 39 targeted commands, including 18 Lake builds, 18 strict module elaborations and the current transitive axiom audit. The manuscript-only command passed and the axiom parser passed all six tests. Every audited declaration depends only on the permitted axioms. The receipt gives each command, exit status, log digest and source identity. [Targeted machine receipt](targeted.json.gz) · [Assertion inventory](../../V81_WSL2_ASSERTIONS/README.md) · [Active correspondence](../../../../FORMALIZATION_STATUS_V81.md)

The full serial run was in progress when this targeted receipt was issued. Its result is recorded separately in the [current verification report](../../../V81_WSL2_LEAN_VERIFICATION.md).

Six supplemental strict queries reproduced the axiom dependencies of all 1,657 named declarations. Recompilation of the two independent Cockett–Hofstra applications and the seven committed statement checks reproduced the identical 19-root proof export. An empty Lean kernel environment accepted it. [Named probes](named-replay.json.gz) · [Export check](cockett-hofstra-replay.json)
