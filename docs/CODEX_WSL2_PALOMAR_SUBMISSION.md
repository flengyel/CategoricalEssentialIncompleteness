# Codex prompt — submit the CEI formalization to Palomar

Work in WSL2 at `/home/flengyel/src/CategoricalEssentialIncompleteness`. Prepare and submit Florian Lengyel’s *Logical consequence and essential incompleteness in recursion categories*. Take the submission through mechanical verification and editorial review. Obtain Florian’s decision on the returned review, then complete registration if he elects to register. Resume an existing attempt whenever possible.

### 1. Establish the source and scope

Fetch the private origin and preserve local and concurrent work. Read `AGENTS.md`, `MANUSCRIPT_CURRENT.json`, `docs/CODEX_WSL2_CURRENT.txt`, `docs/V66_LEAN_WRITING_REPORT.md` and `Lean/formalization.yaml`. Start from the reviewed v70 manuscript or a verified successor. The older v66 handoff documents the preparation run. The exact privately checked proof source was `a65aeb4d5aae48ef9d71bd3352f8935e7612e434`, GitHub Actions run `44869789666`. The submission still needs a full official preflight at its own SHA.

Preserve the names in `Lean/comparator.json`.

| Declaration in `CEIPalomar` | Claim |
| --- | --- |
| `essential_incomplete_iff_inseparable` | Corollary 4.8 in the subobject order, for a disjoint pair whose generated signed theory is consistent. |
| `boolean_assignment` | One closed, consistent, complete extension for all pairs of signed axioms respected by the given Boolean assignment. |
| `exists_inseparable_example` | The existence consequence of Lemma 8.9. The proof uses the PA diagonal pair as witness. |
| `IsNullaryCalculus` | Auxiliary definition identifying the stipulated nullary syntax and deduction data. |

The manuscript guide covers 77 numbered results. Theorem 4.7 supplies the adjunction used in Corollary 4.8. Submit the three configured theorems together in one entry. Preserve the existing account of automation and authorship, and the distinction between the subobject formulation and the printed restriction-idempotent formulation.

### 2. Fix the public repository, tag and commit

The development repository was private when this prompt was written. Check its current visibility, configured remotes, any already authorized public CEI release and active submission. If no public destination is authorized, prepare the release locally and ask Florian to choose between publishing the development repository with its history and a separate public release containing the manuscript and substantive Lean sources. For a separate release, stage the intended files in a clean history, with license, dependency pins, and provenance. Verify that an anonymous checkout has every input required to rebuild. Keep private review records and credentials out of that export.

Choose a fresh, durable release tag **before** composing URLs that refer to this release. The tag may be `cei-v70-palomar` if it is available and v70 is the selected paper. Use the actual public repository and tag in `Lean/formalization.yaml`. Its manuscript URL, location, and all three alignment entries still cite v66 at the starting revision. Check the theorem labels and printed pages in the candidate PDF. In the reviewed manuscript Theorem 4.7 and Corollary 4.8 begin on p. 16 and Lemma 8.9 on p. 52. Keep the historical private check attributed to its tested SHA. Check Appendix E’s 14 distinct proof-source links for public access and correct line ranges. Where the private pin is inaccessible, link the matching Lean passages at the public release tag after comparing their bytes. Follow the manuscript versioning procedure if its files change.

Assemble the paper, PDF, source archive, Lean package, metadata and workflow in one release commit. Record its computed 40-character SHA independently. Bind the tag once. Compare the remote tag’s peeled commit, the recorded SHA, and the commit fetched anonymously from the selected public repository. If a tag already exists at that SHA, reuse it. Resolve a collision with a fresh name and regenerated links. Preserve every issued release tag. Palomar takes the **full SHA**.

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

Compare the candidate Lean sources and dependency pins with the tested proof source. Inspect any differences and run the repository checks they affect. Retain the permitted axioms `propext`, `Quot.sound`, and `Classical.choice`. Apply Palomar’s current source and Challenge requirements to the full checkout. Verify the PDF, the archive and the release links from the published snapshot.

Use `.github/workflows/palomar-preflight.yml`. Check the current [official submission instructions](https://palomar-registry.org/how-to-submit) and [agent protocol](https://submit.palomar-registry.org/llms.txt). The workflow reference and `pipeline_commit` must pin the same supported full pipeline SHA. Use full mode, `palomar-standard-v1`, the wrapper’s 12-character request ID, project `Lean`, configuration `Lean/comparator.json`, and metadata `Lean/formalization.yaml`. With the public repository, verified release tag and candidate SHA set, dispatch the workflow.

```bash
gh workflow run palomar-preflight.yml --repo "$public_repo" --ref "$release_tag" -f "commit=$candidate_sha"
```

Track the matching run through completion. Inspect the mechanical report for `status: pass` and the submitted coordinates. Correct a failure at its source. A change to the released files requires a fresh commit, fresh tag, and fresh preflight.

### 4. Submit, monitor and register

1. Look up the exact registration identity at `https://data.palomar-registry.org/registration-identities/<digest>.json`. Compute SHA-256 over UTF-8 bytes of the lowercase public `owner/repo`, a NUL, `Lean`, a NUL, then `Lean/comparator.json`, with no trailing newline. For a registered candidate, verify the existing version and proceed to citations. For a new commit under the same identity, use its issued ID as `existing_id`. For a new identity, omit that field. Distinguish an authoritative missing record from a failed lookup. Check the private local submission state before starting another intake.
2. Show Florian the exact public repository, full SHA, configuration path and proposed authorization relationship (responsible author or maintainer). Obtain his agreement to those values as required by the service. For an ordinary submission use Palomar’s documented HTTPS and authenticated `gh` flow: `POST /api/submit`, create the one-use verification tag and secret gist, then `POST /api/verify`. Remove just those temporary artifacts after verification. Store the access token privately outside Git so the session can resume. If the account lacks the required access, hand the sign-in step to Florian.
3. Monitor the submission through verification and review at the intervals in the protocol. Report actionable failures and continue after recoverable errors. Retrieve the actual private review with `GET /api/review`. Show Florian its findings and the returned `review_sha256`. Explain that registration publishes the review and creates a permanent record. Obtain his decision on that review. Upon approval, call `POST /register` with that digest and confirm registration after the registry database merge. If the review changes, present the new review for a new decision.
4. Verify the public entry’s ID, numeric version, public repository, SHA, paths and selected declarations. In a subsequent manuscript revision cite the **versioned** entry in E.2 for Corollary 4.8 and the Boolean assignment, and in E.3 for the existential consequence of Lemma 8.9. Retain direct Lean links for the full lemma and the other readings. Rebuild and verify the PDF, ZIP, manifest and correspondence, then sync the private manuscript repository under its standing instructions. Preserve the registered snapshot and tag.

Deliver the public repository and release tag, full SHA, preflight run and report, final submission status, issued versioned entry URL, and follow-up manuscript commit. If waiting on Florian or Palomar, identify the precise decision or pending state and retain the means to resume. Keep access tokens, unregistered reviews and secret status URLs out of committed reports.
