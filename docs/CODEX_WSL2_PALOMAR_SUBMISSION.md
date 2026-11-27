# WSL2 Codex prompt for a synchronized Palomar release

## Reusable prompt

Replace `<edition>` with the author's manuscript version. Give WSL2 Codex the following prompt when authorizing a candidate push to the public repository.

```text
Use my existing local manuscript <edition> of Logical consequence and essential incompleteness in recursion categories. I authorize committing the synchronized candidate and pushing it to flengyel/CategoricalEssentialIncompleteness on origin/main.

Start in /home/flengyel/src/CategoricalEssentialIncompleteness. Before switching branches or integrating remote changes, locate the requested edition and preserve its tracked and untracked source. Inspect git status, git worktree list, and the local manuscript files. The committed manifest identifies the committed edition. If the requested local edition cannot be found, report the paths checked and stop before changing the manuscript.

Fetch origin. Read AGENTS.md and the release procedure with git show origin/main:docs/CODEX_WSL2_PALOMAR_SUBMISSION.md. Use the author's assigned edition commit, or assemble the preserved local edition if it has yet to be committed. Verify that it includes the changes authorized for registration.

Check the public history and pending attempts for PALOMAR-2026-11-22-000009. Keep Appendix E’s citations to the published v3 entry and its registered Solution.lean, and check the other proof links against their cited source revisions. Use the edition’s manuscript PDF URL in Lean/formalization.yaml. Verify that its source ref resolves to the exact candidate commit.

Check the complete PDF, source archive, manifest, correspondence and metadata. If the author has already fixed the edition at a public commit, use that full SHA. If authorized corrections are needed, commit and push them together and record the new full SHA. Bind an unused permanent release tag to the candidate once and verify its remote peeled SHA. Run the WSL2 replay and obtain two independent whole-paper readings on the same SHA under AGENTS.md.

Run the official full Comparator preflight on the candidate SHA with project Lean, configuration Lean/comparator.json and metadata Lean/formalization.yaml. After it passes, obtain my intake approval for that SHA. Submit under the existing ID or resume a matching attempt. Present the complete private review and digest for my registration decision. After registration, verify the public receipt against the candidate. Archive the run, receipt and reports in a separate evidence commit that names the tested commit.
```

## Release procedure

### 1. Establish the source and scope

After locating and preserving the requested local edition, fetch `origin/main` for `flengyel/CategoricalEssentialIncompleteness` and read `AGENTS.md`, `MANUSCRIPT_CURRENT.json`, `docs/CODEX_WSL2_CURRENT.txt` and `Lean/formalization.yaml`. Read the latest public record for `PALOMAR-2026-11-22-000009` and identify its registered source commit and manuscript edition. A later commit may have added the registry citation. Preserve the registered snapshot and its tag. When the author has named an edition commit, fetch that commit and use a detached worktree. If the local edition includes changes the author wants registered, preserve and integrate them before fixing the new candidate SHA.

Preserve the names in `Lean/comparator.json`.

| Declaration in `CEIPalomar` | Claim |
| --- | --- |
| `essential_incomplete_iff_inseparable` | Corollary 4.8 in the subobject order, for a disjoint pair whose generated signed theory is consistent. |
| `boolean_assignment` | One closed, consistent, complete extension for all pairs of signed axioms respected by the given Boolean assignment. |
| `exists_inseparable_example` | The existence consequence of Lemma 8.9. The proof uses the PA diagonal pair as witness. |
| `IsNullaryCalculus` | Auxiliary definition identifying the first-order calculus with propositional atoms specified by an object and the stipulated deduction data. |

The manuscript guide covers 77 numbered results. Theorem 4.7 supplies the adjunction used in Corollary 4.8. Submit the three configured theorems together in one entry. Preserve the account of automation and authorship. Check how the candidate manuscript states Corollary 4.8. The Comparator theorem uses subobjects, and `ManuscriptChecks.essentiallyIncomplete_iff_inseparable_domains` transports it to restriction idempotents.

### 2. Fix the public repository, tag and commit

Follow the fixed-tag procedure used for the [Došen–Petrić v25 / Palomar v3 candidate](https://github.com/flengyel/Dosen-Petric-Maximality/blob/874ea6bcd775ff21f7a84759f46adc1d3364a954/docs/PALOMAR_V25_CODEX_HANDOFF.md). Read the public version history for `PALOMAR-2026-11-22-000009` and check for a pending attempt for the same entry. Use the next version after the latest registered one as the proposed target. Resolve an unavailable history or competing attempt before choosing the target. Palomar assigns the version at registration.

Appendix E cites published work. For editions citing the v3 registration, retain its permalink in E.2 and E.3, the two links to the registered solution at `cei-v72-palomar-v3`, and the existing source links for the other proofs. Check the printed theorem numbers, page locators and linked Lean declarations in the rendered manuscript and metadata.

Check the PDF selected by `MANUSCRIPT_CURRENT.json`, its source archive and the whole-paper correspondence. If the edition is already committed, verify those files at the assigned full SHA. If corrections are necessary, rebuild the PDF and archive, update the manifest and correspondence, and commit all candidate changes together. Push the candidate when authorized. Choose an unused durable release tag, bind it once to the exact SHA, and check the tag’s peeled value on the remote. Independently resolve the manuscript PDF URL in `Lean/formalization.yaml` and compare its commit and PDF bytes with the candidate. If that URL uses a dedicated edition branch, keep that branch fixed at the candidate. Preserve existing tags.

### 3. Verify and run the official preflight

In a clean detached WSL2 worktree at the full candidate SHA, run the full replay and complete the two independent whole-paper readings required by `AGENTS.md` and the edition handoff. Retain the kernel receipt, command log and both reports with that SHA. Run the following Palomar-specific checks in the same worktree.

```bash
python3 scripts/verify.py --manuscript-only
(
  cd Lean
  lake build +CEIPalomar.Challenge +CEIPalomar.Solution +CEIPalomar.ManuscriptChecks
  lake env lean -DwarningAsError=true ../scripts/check_cei_challenge.lean
  lake env lean -DwarningAsError=true CEIPalomar/ManuscriptChecks.lean
)
```

Compare the candidate Lean sources and dependency pins with the source commit of the latest registered version. Inspect any differences and run the repository checks they affect. Retain the permitted axioms `propext`, `Quot.sound`, and `Classical.choice`. Apply Palomar’s current source and Challenge requirements to the full checkout. Verify the PDF, the archive and the release links from the published snapshot.

Use `.github/workflows/palomar-preflight.yml`. Check the current [official submission instructions](https://palomar-registry.org/how-to-submit) and [agent protocol](https://submit.palomar-registry.org/llms.txt). The workflow reference and `pipeline_commit` must pin the same supported full pipeline SHA. Use full mode, `palomar-standard-v1`, the wrapper’s 12-character request ID, project `Lean`, configuration `Lean/comparator.json`, and metadata `Lean/formalization.yaml`. With the public repository, verified release tag and candidate SHA set, dispatch the workflow.

```bash
gh workflow run palomar-preflight.yml --repo "$public_repo" --ref "$release_tag" -f "commit=$candidate_sha"
```

Track the matching run through completion. Verify the full candidate SHA and paths in the mechanical report, its passing status and the Comparator outcome. Record the run ID and URL with that report. An earlier run certifies only its recorded commit. If the candidate changes, repeat its verification and preflight under a fresh permanent tag.

### 4. Submit, monitor and register

1. Check the private local submission state for this candidate. Resume a matching attempt. If the candidate is already registered, check the receipt as in step 4. For an ordinary new version submit with `existing_id=PALOMAR-2026-11-22-000009`, the full candidate SHA and the three CEI paths used in preflight.

2. Show Florian the exact public repository, full SHA, configuration path and proposed authorization relationship (responsible author or maintainer). Obtain his agreement to those values as required by the service. For an ordinary submission use Palomar’s documented HTTPS and authenticated `gh` flow: `POST /api/submit`, create the one-use verification tag and secret gist, then `POST /api/verify`. Remove just those temporary artifacts after verification. Store the access token privately outside Git so the session can resume. If the account lacks the required access, hand the sign-in step to Florian.
3. Monitor the submission through verification and review at the intervals in the protocol. Report actionable failures and continue after recoverable errors. Retrieve the actual private review with `GET /api/review`. Show Florian its findings and the returned `review_sha256`. Explain that registration publishes the review and creates a permanent record. Obtain his decision on that review. Before registration, recheck that the target version is still next. If it has changed, stop and report the conflict. Upon approval of that review, call `POST /register` with its digest and confirm registration after the registry database merge. If the review changes, present the new review for a new decision.
4. Compare the issued public record and receipt against the approved submission. Verify the entry ID, assigned version, permanent URL, source repository and full SHA, project paths and selected declarations. Resolve the registry’s manuscript link and compare the linked PDF with the candidate manifest. Appendix E’s v3 citations continue to identify the previously registered proofs. Report any discrepancy and preserve the released tag and candidate.

Return the receipt, permanent entry URL, manuscript edition, release tag, registered SHA and Comparator run URL to the author. Archive the public verification report and receipt in a later evidence-only commit and identify both SHAs. This records the run performed on the submitted bytes while preserving the manuscript and YAML in the tested commit. Keep access tokens, unregistered reviews and secret status URLs out of committed reports.
