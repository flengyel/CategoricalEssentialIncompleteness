# WSL2 verification of manuscript v91

Fetch `origin/main` and record the tested commit. The [manifest](../MANUSCRIPT_CURRENT.json) identifies the v91 PDF and sources. [Whole-paper correspondence](../FORMALIZATION_STATUS_V91.md)

1. For Appendix D, match Theorem D.1 and Corollary D.2, the strictly commuting square, the numeral-observation inclusion and the true-arithmetic isomorphism. Check the c.e. assumption on `unprimed_not_locallyConnected` separately from the hypotheses of Corollary D.2. The [v90 handoff](CODEX_WSL2_CEI_V90_LEAN_HANDOFF.md) lists the preceding Appendix B checks.
2. Run `python3 scripts/test_verify_axiom_parser.py`, `python3 scripts/verify.py --manuscript-only` and `bash scripts/verify-wsl.sh` with the pinned toolchain. Record command results, measured inputs, transitive axioms and the tested commit. [Last full kernel receipt](V84_WSL2_LEAN_VERIFICATION.json.gz)
3. Record and reconcile two independent full manuscript readings at the tested revision, with links to the kernel receipt and correspondence under [AGENTS.md](../AGENTS.md).
