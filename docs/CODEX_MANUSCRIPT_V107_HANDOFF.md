# Manuscript v107

The introduction explains how first-order formulas are formed, identifies sentences as the formulas with no free variables, and describes how an assignment of target sentences to atoms extends to all first-order formulas. Section 1.2 specifies the bounds on a separator of the diagonal domains. Section 1.3 explains how a parameter stays fixed in a derivation. Sections 1, 2 and 4 distinguish restriction idempotents from the subobjects represented by their splittings and state when all subobjects arise this way.

## WSL2 verification and private intake

Florian Lengyel selected the published v107 edition for the next version of Palomar entry `PALOMAR-2026-11-22-000009`. The responsible author or maintainer is Florian Lengyel. Use these exact inputs in WSL2.

| Input | Value |
| --- | --- |
| Public repository | `flengyel/CategoricalEssentialIncompleteness` |
| Candidate commit | `569f67d655e9c7024a0b6637ca707d43ac745bd4` |
| Edition branch | `cei-manuscript-v107` |
| Project, Comparator configuration, metadata | `Lean`, `Lean/comparator.json`, `Lean/formalization.yaml` |

1. Preserve local work. Fetch the handoff from `origin/main` and the candidate from the edition branch. Verify that the branch resolves to the full SHA above and use a clean detached worktree at that SHA. The later handoff on main supersedes the hold found inside the frozen snapshot. Read [AGENTS.md](../AGENTS.md) and the [submission procedure](CODEX_WSL2_PALOMAR_SUBMISSION.md).
2. Check the public registry history and the private local receipts for this entry. Reuse a matching v107 attempt if one exists; if v107 is already registered, verify its receipt. The author handles any withdrawal of v103 or v104. If an older pending attempt conflicts, show the author its actual status privately. An earlier intake acceptance does not establish public registration. Follow §2 of the submission procedure to verify a permanent release tag at the candidate SHA.
3. In the detached worktree, run the full serial Lean replay, the two independent whole-paper readings and the Palomar-specific checks in §3 of the procedure. In the v107 revisions check the distinction between restriction idempotents and subobjects under the partial-inverse hypothesis, and between assignments of closed sentences to atoms and translation of all first-order formulas. Retain the receipt and both reading reports. Run the official full Comparator preflight on the same commit and confirm its mechanical report records a pass at that SHA.
4. Resolve the PDF URL in the candidate YAML. Its bytes must match the v107 manifest (SHA-256 `6fe6733a9266563a5a18c36ce06b127cfc11200f5f3934426b27221ac63794fc`). Theorem 4.7 spans pp. 22–23, with initiality on p. 22. Corollary 4.8 starts on p. 23, its Boolean construction is on p. 24, and Lemma 8.9 is on p. 63. Check the parsed YAML description against the two paragraphs in `docs/PALOMAR_ABSTRACT.txt` (SHA-256 `93bfd976d844fefaece566254ab9db6e30b230e98836a947397d74f3b21f8dd6`, without the final newline). Check the pinned renderer’s extraction of “Notes from the statement file” separately against the opening module comment of `Lean/CEIPalomar/Challenge.lean` (SHA-256 `e12cd7d9831f1e91a6ead9803514ccda083a4ed936c4db3be42090818b86339e`).
5. After the checks pass, use the author’s intake approval for the repository, SHA, paths and relationship above. Follow §4 of the procedure for an ordinary new version of the existing entry. Monitor the v107 attempt and check its hosted metadata. Return the complete private review and its own `review_sha256` to Florian privately. Await his approval of that digest before public registration. Keep public verification reports in a separate evidence commit. The reviewed SHA must still be the source in the eventual registration receipt.

[Edition PDF](../manuscript/logical_consequence_and_essential_incompleteness_v107.pdf) · [LaTeX source](../manuscript/logical_consequence_v107_source.zip) · [Lean correspondence](../FORMALIZATION_STATUS_V107.md)
