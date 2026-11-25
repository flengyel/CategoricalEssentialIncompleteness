# WSL2 verification of manuscript v86

Run one full verification on the active v86 sources. The entire v85 Lean and verifier trees coincide with those tested for v84 at `b37f8908435a4c2991af5b95de4645980ac60a05`. No separate replay of the superseded v85 manuscript is needed.

1. Fetch `origin/main`, select a clean revision containing [the v86 manifest](../MANUSCRIPT_CURRENT.json), and record its full SHA. Verify the selected files against that manifest and the [whole-paper correspondence](../FORMALIZATION_STATUS_V86.md).
2. Check the use of `IsSection.isRange` and `rangesOfChoice` in §1, the indices in `machine_section` and `parameter_indices` against `machine_no_lift` in Appendix C, and the uniform independent-sentence conclusion in §8.3. Carry forward the v85 selector and slice-functor checks.
3. At that revision run `python3 scripts/test_verify_axiom_parser.py`, `python3 scripts/verify.py --manuscript-only`, and `bash scripts/verify-wsl.sh` with the pinned toolchain. Retain the command results, measured inputs, transitive axioms of current and retained declarations, and the full tested SHA. [Previous kernel receipt](V84_WSL2_LEAN_VERIFICATION.json.gz)
4. Reconcile two independent full readings of the tested revision as required by [AGENTS.md](../AGENTS.md). Link each report to that revision, its correspondence and its kernel receipt. The v86 referee and writing review records the editorial changes and primary-source checks. The edition-specific kernel receipt and the two qualifying reports are pending.
