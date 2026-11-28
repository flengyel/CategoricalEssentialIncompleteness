# WSL2 handoff for manuscript v104

**Submission on hold by the author, 27 November 2026.** Stop before any further Palomar intake or registration action. The author is handling the withdrawal of v103 and v104. Preserve their receipts. Await the author’s explicit restart. This instruction supersedes the procedure below and the earlier prompt for this edition. [Current hold](CODEX_WSL2_CURRENT.txt)

The author reports that Palomar accepted the v103 submission. Registration is paused. Preserve that submission, its private review and its digest at `f4b8921ecedb388c8b22e8f6e72df608abafa9f9`. Only v104 is eligible for this submission. Leave v103 unregistered and retain its receipts. [Current instructions](CODEX_WSL2_CURRENT.txt)

The v103 full replay, two independent readings and Comparator run 45931283651 tested that same commit. The report commit is `8f7c1447f1b2af29d73b2b7a9ff9098aeb58a7f6`. [Verification report](V103_WSL2_LEAN_VERIFICATION.md) · [Comparator report](palomar/v103-preflight/mechanical-report.json)

## Verify v104 in WSL2

Use the full SHA in the author’s handoff. Fetch `origin/main` and `origin/cei-manuscript-v104`. Check that the edition branch resolves to the supplied SHA and that this commit is an ancestor of `origin/main`. Create a clean detached worktree at that SHA and check that `MANUSCRIPT_CURRENT.json` selects v104.

1. Use the existing serial build lock and the pinned toolchain. Run `lake exe cache get` in `Lean/`, then run `python3 scripts/test_verify_axiom_parser.py`, `python3 scripts/verify.py --manuscript-only` and `bash scripts/verify-wsl.sh` in the repository root. Retain the complete log, kernel receipt and axiom audit.
2. Run the project’s official full Comparator preflight as in [§3 of the submission procedure](CODEX_WSL2_PALOMAR_SUBMISSION.md#3-verify-and-run-the-official-preflight), using `cei-manuscript-v104` as the workflow ref and the full edition SHA as its commit input. Check that the mechanical report records that SHA, the SHA-256 of the candidate YAML, and a passing Comparator result.
3. Compare the YAML description, statement-file notes and PDF locators with the values below. Resolve the manuscript URL in the YAML and verify the PDF against the manifest. Return both receipts, the tested SHA and the preflight run URL. Use a separate evidence commit for any published verification reports.

The author’s manuscript reviews take place in chat. [Correspondence](../FORMALIZATION_STATUS_V104.md)

The v104 registry description is the two paragraphs of [PALOMAR_ABSTRACT.txt](PALOMAR_ABSTRACT.txt), without the terminal newline. Its SHA-256 is `93bfd976d844fefaece566254ab9db6e30b230e98836a947397d74f3b21f8dd6`. “Notes from the statement file” comes from the opening module comment of [Challenge.lean](../Lean/CEIPalomar/Challenge.lean). The v103 receipt records the SHA-256 of that text as `e12cd7d9831f1e91a6ead9803514ccda083a4ed936c4db3be42090818b86339e`. These two hashes identify different fields. Palomar's private-review digest belongs to the particular submission that returned it.

Theorem 4.7 spans pp. 22–24, with its initiality clause on p. 23. Corollary 4.8 and its Boolean construction are on p. 24. Lemma 8.9 is on p. 64.

## Submit v104 for private review

After verification passes, use the intake procedure in [§4](CODEX_WSL2_PALOMAR_SUBMISSION.md#4-submit-monitor-and-register) to submit an ordinary new version of `PALOMAR-2026-11-22-000009`. Use the same full v104 SHA tested above in `flengyel/CategoricalEssentialIncompleteness`, the project path `Lean`, Comparator configuration `Lean/comparator.json`, and metadata `Lean/formalization.yaml`. The author is a responsible author or maintainer of the formalization. Resume an existing attempt only if its source is this exact v104 commit. If the service requires withdrawing v103 first, preserve its private review and request the author’s withdrawal approval.

Check the v104 submission’s reported source SHA and paths. Compare the rendered description and statement-file notes with their separate expected values. Return the v104 private review and its own `review_sha256` to the author privately. Stop before public registration until the author approves that review.
