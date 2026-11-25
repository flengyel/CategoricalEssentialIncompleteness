# WSL2 verification of manuscript v92

Fetch `origin/main` and record the tested commit. The [manifest](../MANUSCRIPT_CURRENT.json) identifies the v92 PDF and sources. [Whole-paper correspondence](../FORMALIZATION_STATUS_V92.md)

1. Compare the seven worked arguments in Appendix E with the linked Lean declarations. For the two extended ranges in E.7 check sentence membership in the theorem domain and both inclusions in the recovery of an arbitrary axiom image. The hypotheses and conclusions of Lemma A.7 are recorded in the [v89 review](reviews/V89_REFEREE_AND_WRITING/README.md). The [v91 handoff](CODEX_WSL2_CEI_V91_LEAN_HANDOFF.md) covers Appendix D.
2. Run `python3 scripts/test_verify_axiom_parser.py`, `python3 scripts/verify.py --manuscript-only` and `bash scripts/verify-wsl.sh` with the pinned toolchain. Record command results, measured inputs, transitive axioms and the tested commit. [Last full kernel receipt](V84_WSL2_LEAN_VERIFICATION.json.gz)
3. Record and reconcile two independent full manuscript readings at the tested revision, with links to the kernel receipt and correspondence under [AGENTS.md](../AGENTS.md).
