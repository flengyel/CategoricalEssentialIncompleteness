# Codex prompt — submit the CEI formalization to Palomar

Work in WSL2 at `/home/flengyel/src/CategoricalEssentialIncompleteness`. Prepare and submit Florian Lengyel’s *Logical consequence and essential incompleteness in recursion categories*. Take the submission through mechanical verification and editorial review. Obtain Florian’s decision on the returned review, then complete registration if he elects to register. Resume an existing attempt whenever possible.

### 1. Establish the source and scope

Fetch `origin/main` for `flengyel/CategoricalEssentialIncompleteness`, preserve local and concurrent work, and read `AGENTS.md`, `MANUSCRIPT_CURRENT.json`, `docs/CODEX_WSL2_CURRENT.txt` and `Lean/formalization.yaml`. [Palomar version 2](palomar/PALOMAR-2026-11-22-000009-v2/README.md) records `cd08f0a42a6e8e182805db84396e40fdddc1b2ca`, which contains manuscript v70. Manuscript v71 at `170f14c13366e1a10dca9a77fc6fda4cd1c8acda` added the v2 citation. Preserve both snapshots. Prepare the next authorized submission from current main.

Preserve the names in `Lean/comparator.json`.

| Declaration in `CEIPalomar` | Claim |
| --- | --- |
| `essential_incomplete_iff_inseparable` | Corollary 4.8 in the subobject order, for a disjoint pair whose generated signed theory is consistent. |
| `boolean_assignment` | One closed, consistent, complete extension for all pairs of signed axioms respected by the given Boolean assignment. |
| `exists_inseparable_example` | The existence consequence of Lemma 8.9. The proof uses the PA diagonal pair as witness. |
| `IsNullaryCalculus` | Auxiliary definition identifying the stipulated nullary syntax and deduction data. |

The manuscript guide covers 77 numbered results. Theorem 4.7 supplies the adjunction used in Corollary 4.8. Submit the three configured theorems together in one entry. Preserve the existing account of automation and authorship, and the distinction between the subobject formulation and the printed restriction-idempotent formulation.

### 2. Fix the public repository, tag and commit

Follow the fixed-tag procedure used for the [Došen–Petrić v25 / Palomar v3 candidate](https://github.com/flengyel/Dosen-Petric-Maximality/blob/874ea6bcd775ff21f7a84759f46adc1d3364a954/docs/PALOMAR_V25_CODEX_HANDOFF.md). Read the public version history for `PALOMAR-2026-11-22-000009` and check for a pending attempt for the same entry. If v2 is still the latest version, the target is [Palomar v3](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-22-000009&version=3). Resolve an unavailable history or competing attempt before choosing the target. Palomar assigns the version at registration.

Choose an unused durable tag name for the candidate before composing its GitHub links. In Appendix E.2 place the target version’s permalink beside the subobject formulation of Corollary 4.8 and the Boolean-assignment theorem. In E.3 place it beside the existential consequence of Lemma 8.9 and retain the direct Lean proof link for the full lemma. Use a neutral citation such as “Palomar entry …, version …” that can stand in the candidate before registration and in the same PDF afterwards. Use the candidate tag in Appendix E’s links to this release’s Lean proofs and in the manuscript PDF URL in `Lean/formalization.yaml`. Check each proof’s line range and the manuscript edition, theorem labels and printed pages in the metadata and correspondence table.

Build the complete manuscript, including all six subsections of Appendix E. Check them in the rendered PDF, extract and check the two versioned PDF hyperlinks in E.2 and E.3, and confirm that the source archive contains the same appendix as the checkout. Update the current PDF, source archive, manifest and correspondence table under the repository’s manuscript versioning instructions. Commit these files together with the intended Lean source and metadata in one release snapshot. Record the full computed SHA in the handoff, push the candidate to `origin/main` when authorized and bind the chosen tag once to that SHA. Check the remote tag’s peeled commit and the candidate fetched from the public repository against the recorded SHA. Resolve a tag collision with a fresh name and regenerated links. Preserve all existing release tags.

### 3. Verify and run the official preflight

Use the pinned toolchain and run the following in the candidate checkout.

```bash
python3 scripts/verify.py --manuscript-only
(
  cd Lean
  lake build +CEIPalomar.Challenge +CEIPalomar.Solution +CEIPalomar.ManuscriptChecks
  lake env lean -DwarningAsError=true ../scripts/check_cei_challenge.lean
  lake env lean -DwarningAsError=true CEIPalomar/ManuscriptChecks.lean
)
```

Compare the candidate Lean sources and dependency pins with the registered v2 source. Inspect any differences and run the repository checks they affect. Retain the permitted axioms `propext`, `Quot.sound`, and `Classical.choice`. Apply Palomar’s current source and Challenge requirements to the full checkout. Verify the PDF, the archive and the release links from the published snapshot.

Use `.github/workflows/palomar-preflight.yml`. Check the current [official submission instructions](https://palomar-registry.org/how-to-submit) and [agent protocol](https://submit.palomar-registry.org/llms.txt). The workflow reference and `pipeline_commit` must pin the same supported full pipeline SHA. Use full mode, `palomar-standard-v1`, the wrapper’s 12-character request ID, project `Lean`, configuration `Lean/comparator.json`, and metadata `Lean/formalization.yaml`. With the public repository, verified release tag and candidate SHA set, dispatch the workflow.

```bash
gh workflow run palomar-preflight.yml --repo "$public_repo" --ref "$release_tag" -f "commit=$candidate_sha"
```

Track the matching run through completion. Inspect the mechanical report for `status: pass` and the submitted coordinates. Correct a failure at its source. A change to the released files requires a fresh commit, fresh tag, and fresh preflight.

### 4. Submit, monitor and register

1. Check the private local submission state for this candidate. Resume a matching attempt. If the candidate is already registered, check the receipt as in step 4. For an ordinary new version submit with `existing_id=PALOMAR-2026-11-22-000009`, the full candidate SHA and the three CEI paths used in preflight.

2. Show Florian the exact public repository, full SHA, configuration path and proposed authorization relationship (responsible author or maintainer). Obtain his agreement to those values as required by the service. For an ordinary submission use Palomar’s documented HTTPS and authenticated `gh` flow: `POST /api/submit`, create the one-use verification tag and secret gist, then `POST /api/verify`. Remove just those temporary artifacts after verification. Store the access token privately outside Git so the session can resume. If the account lacks the required access, hand the sign-in step to Florian.
3. Monitor the submission through verification and review at the intervals in the protocol. Report actionable failures and continue after recoverable errors. Retrieve the actual private review with `GET /api/review`. Show Florian its findings and the returned `review_sha256`. Explain that registration publishes the review and creates a permanent record. Obtain his decision on that review. Before registration, recheck that the target version is still next. If it has changed, stop and report the conflict. Upon approval of that review, call `POST /register` with its digest and confirm registration after the registry database merge. If the review changes, present the new review for a new decision.
4. Compare the receipt and issued public record with the candidate. The entry ID, numeric version, versioned URL, source repository and full SHA, project paths and selected declarations must agree. Verify that the permanent link embedded in the tagged PDF opens that version and the registry’s manuscript link opens that PDF. If the assigned version or SHA differs, stop publication and report both values. Preserve the released tag and candidate.

Return the receipt, permanent entry URL, manuscript edition, release tag, registered source SHA and verification run to the originating manuscript chat. Archive the public verification report in a separate commit. Identify that report commit separately in the handoff. Keep access tokens, unregistered reviews and secret status URLs out of committed reports.
