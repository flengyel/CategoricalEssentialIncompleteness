# Lean verification of manuscript v103

The full serial Lean replay passed on `f4b8921ecedb388c8b22e8f6e72df608abafa9f9`, the v103 candidate for Florian Lengyel’s *Logical consequence and essential incompleteness in recursion categories*. All 2,101 commands exited 0. Both independent whole-paper readings found zero mathematical errors, zero ambiguities, zero Lean omissions and zero proof gaps. The official full Palomar Comparator preflight passed on the same source. [Tested source](https://github.com/flengyel/CategoricalEssentialIncompleteness/tree/f4b8921ecedb388c8b22e8f6e72df608abafa9f9) · [Tested correspondence](https://github.com/flengyel/CategoricalEssentialIncompleteness/blob/f4b8921ecedb388c8b22e8f6e72df608abafa9f9/FORMALIZATION_STATUS_V103.md) · [Kernel receipt](V103_WSL2_LEAN_VERIFICATION.json.gz) · [First reading](reviews/V103_WSL2_AUDITS/reader-one/REPORT.md) · [Second reading](reviews/V103_WSL2_AUDITS/reader-two/REPORT.md) · [Comparator run](https://github.com/flengyel/CategoricalEssentialIncompleteness/actions/runs/45931283651)

## Pinned replay

The fetched `cei-v103-palomar-candidate` branch and the clean detached checkout both resolved to the tested SHA. The manifest selected v103 before the run. The wrapper recorded start commit `f4b8921ecedb388c8b22e8f6e72df608abafa9f9`, an empty starting diff and exit status **0**. It ran from 2026-11-27T02:04:28Z to 2026-11-27T07:49:50Z (5 h 45 min 22 s). The Lean toolchain was `leanprover/lean4:v4.35.0-rc2`. The replay used its own copies of the project build and pinned dependency worktrees, with `LEAN_NUM_THREADS=1` and the repository’s serial build lock. [Handoff](https://github.com/flengyel/CategoricalEssentialIncompleteness/blob/f4b8921ecedb388c8b22e8f6e72df608abafa9f9/docs/CODEX_WSL2_CEI_V103_LEAN_HANDOFF.md) · [Exact wrapper output](V103_WSL2_LEAN_VERIFICATION.log.gz)

| Checks executed | Result |
| --- | --- |
| `lake exe cache get` in `Lean` | Exit 0. |
| `python3 scripts/test_verify_axiom_parser.py` | Six tests, exit 0. |
| `python3 scripts/verify.py --manuscript-only` | Source, PDF, source archive and correspondence passed, exit 0. |
| `lake build +CEIPalomar.Challenge +CEIPalomar.Solution +CEIPalomar.ManuscriptChecks` | Exit 0. |
| `lake env lean -DwarningAsError=true ../scripts/check_cei_challenge.lean` | Exit 0. Checked the four designated placeholders and 2,695 transitive Challenge imports. |
| `lake env lean -DwarningAsError=true CEIPalomar/ManuscriptChecks.lean` | Exit 0. Checked the transitive axioms of 56 package and recovery declarations. |
| `bash scripts/verify-wsl.sh` | Exit 0. 2,093 strict module elaborations, the current statement check, project build and both transitive axiom inventories. |

All 16 dependency worktrees were clean at their manifest revisions at the start and finish. The verifier measured 2,745 input files. The receipt includes the native machine report, the command vectors, output and SHA-256 for each log, the input hashes and Git objects, and the manuscript and package checks. [Kernel receipt](V103_WSL2_LEAN_VERIFICATION.json.gz) · [Pinned verification program](https://github.com/flengyel/CategoricalEssentialIncompleteness/blob/f4b8921ecedb388c8b22e8f6e72df608abafa9f9/scripts/verify.py)

The current inventory covers 35,112 declarations in 1,174 production modules. The retained inventory covers 1,274 declarations. The inventories have 0 declaration names in common. A declaration may depend on several permitted axioms.

| Transitive axiom | Current declarations | Retained declarations |
| --- | ---: | ---: |
| `Classical.choice` | 27,125 | 1,221 |
| `Quot.sound` | 27,582 | 1,232 |
| `propext` | 29,320 | 1,251 |

Separately, strict elaboration of `Tests/AxiomRegression.lean` exited 0. Each of its three Rice–Shapiro results used only `propext`, within their two-axiom allowance of `propext` and `Quot.sound`. The comparator configuration for the three selected CEI theorems and `IsNullaryCalculus` permits `propext`, `Quot.sound` and `Classical.choice`. The kernel receipt contains the exact supplemental command and output under `rice_shapiro_regression`. [Comparator configuration](https://github.com/flengyel/CategoricalEssentialIncompleteness/blob/f4b8921ecedb388c8b22e8f6e72df608abafa9f9/Lean/comparator.json) · [Rice–Shapiro regression](https://github.com/flengyel/CategoricalEssentialIncompleteness/blob/f4b8921ecedb388c8b22e8f6e72df608abafa9f9/Lean/Tests/AxiomRegression.lean)

## Manuscript and readings

The revised preface uses Lemma 8.1 for the primitive-recursive map to sentence codes. In Corollary 8.4 a recursive separator pulls back along that map. An index for the conditional on the inverse image gives a partial morphism with that standard interpretation, which Corollary 3.2 excludes. The two adjunctions of Theorem 5.2 hold on the underlying categories. In Corollary 9.4 each representation computes a separator, while no single program computes one fixed separator for every representation. In the three-point example, the computable component decisions commute with both morphisms out of the middle vertex. The result at either endpoint quantifies over consistent extensions in the same language with c.e. axioms. [Preface](https://github.com/flengyel/CategoricalEssentialIncompleteness/blob/f4b8921ecedb388c8b22e8f6e72df608abafa9f9/manuscript/latex/preface.tex) · [First reading](reviews/V103_WSL2_AUDITS/reader-one/REPORT.md) · [Second reading](reviews/V103_WSL2_AUDITS/reader-two/REPORT.md)

The §1.1 comparison invokes the result of Murwanashyaka, Pakhomov and Visser on choosing the signs of all class-size sentences. For each set of positive indices, the readers checked the biconditional between recursiveness of that set and computable enumerability of the resulting theory. They also checked that adjoining exactly those signs gives the same provable sentences as the theory of the canonical model, for every native sentence. These supplemental proofs were written during review and compiled against the pinned v103 imports. The second report archives their source and separate kernel logs. [All-sentence proof](reviews/V103_WSL2_AUDITS/reader-two/SignedCompleteness.lean.txt) · [Additional applications](reviews/V103_WSL2_AUDITS/reader-two/Applications.lean.txt) · [Supplemental receipt](reviews/V103_WSL2_AUDITS/reader-two/APPLICATION-RECEIPT.json)

The 107-page PDF and source ZIP fetched through the public candidate branch agree byte for byte with the Git objects and manifest. The archive contains the same Appendix E as the checkout. All seven Appendix E subsections appear on pp. 102–105. Both version-specific registry links occur on p. 103. The two registered Solution ranges resolve at v72. All nineteen remaining ranges resolve at their cited source tag. [Candidate PDF](https://github.com/flengyel/CategoricalEssentialIncompleteness/blob/cei-v103-palomar-candidate/manuscript/logical_consequence_and_essential_incompleteness_v103.pdf) · [Appendix E evidence](reviews/V103_WSL2_AUDITS/reader-one/APPENDIX_E.json) · [Published v3 entry](https://palomar-registry.org/entry?id=PALOMAR-2026-11-22-000009&version=3)

## Palomar metadata and official preflight

The parsed two-paragraph YAML description matches `docs/PALOMAR_ABSTRACT.txt` exactly after removing the text file’s final newline. Its first paragraph matches the 1,891-character manuscript abstract after conversion of the TeX notation. The second identifies the three selected statements. The SHA-256 of the parsed description is `264bef5289fc443458be4e64e73d9d692cce9cc62cbf310eb5a91aaaf18be2d0`. The pinned Palomar renderer’s opening-comment extractor gives `e12cd7d9831f1e91a6ead9803514ccda083a4ed936c4db3be42090818b86339e` for “Notes from the statement file.” This is the local check of the text that Palomar uses for `module_doc`. The official preflight produced a mechanical-report artifact. Hosted rendering belongs to a later intake stage. [Approved text](https://github.com/flengyel/CategoricalEssentialIncompleteness/blob/f4b8921ecedb388c8b22e8f6e72df608abafa9f9/docs/PALOMAR_ABSTRACT.txt) · [Statement file](https://github.com/flengyel/CategoricalEssentialIncompleteness/blob/f4b8921ecedb388c8b22e8f6e72df608abafa9f9/Lean/CEIPalomar/Challenge.lean) · [Official extractor](https://github.com/PalomarRegistry/PalomarSubmission/blob/046554302064b2c83c2b924bea6db87fc5900c68/scripts/render_challenge.py#L583-L598)

| Metadata reference | Printed location |
| --- | --- |
| Theorem 4.7 and its proof | pp. 22–24 |
| Initiality with the atomic assignment on all of X | p. 23 |
| Corollary 4.8 and the Boolean assignment constructing a complete consistent extension | p. 24 |
| Lemma 8.9 under the consistency of PA, whose arithmetic witness gives the existential declaration | p. 64 |

GitHub ran the full workflow on the dedicated candidate branch with `project_path=Lean`, `comparator_config_path=Lean/comparator.json` and `formalization_metadata_path=Lean/formalization.yaml`. The workflow reference and pipeline input both pin `046554302064b2c83c2b924bea6db87fc5900c68`. The report records `status: pass` with no errors or warnings, profile `palomar-standard-v1`, the tested source SHA, and metadata SHA-256 `9ad1cde711c01c82663f329c538a0acff7b602766dc87582ae309648f752dacd`. Palomar checked 2,732 Lean sources. Comparator reported acceptance by nanoda and Lean’s default kernel. The additional con-ron check accepted 24,250 declarations. The archived mechanical report has SHA-256 `f5ed177b90d80346eb971cfb26389313f626e0bf41fa53e4076b5b77b9c620d7`. [Official run](https://github.com/flengyel/CategoricalEssentialIncompleteness/actions/runs/45931283651) · [Official artifact](https://github.com/flengyel/CategoricalEssentialIncompleteness/actions/runs/45931283651/artifacts/15169746146) · [Archived mechanical report](palomar/v103-preflight/mechanical-report.json)

The last cited registration is v3 at `efda31344ec6420142468ab28af9d96deab571e7`. Its four CEIPalomar source files differ from v103 only in documentation. The dependency pins and comparator configuration agree. The rest of the Lean project includes subsequent proof development covered by this v103 replay. This verification ended before intake. [Registered v3 record](https://palomar-registry.org/entry?id=PALOMAR-2026-11-22-000009&version=3) · [Candidate metadata](https://github.com/flengyel/CategoricalEssentialIncompleteness/blob/f4b8921ecedb388c8b22e8f6e72df608abafa9f9/Lean/formalization.yaml)

| Evidence file | SHA-256 |
| --- | --- |
| Compressed kernel receipt | `f8e6a4ed3f58b5eb5d54a781b1493742de5d077159d9b0e5d8fef7156d2f65d3` |
| Native verification JSON, reproduced in the receipt | `5e609228a7c6b7900c49808ff9f5f211ec8b758c14aa89dbccda9b36d6bc6ece` |
| Complete uncompressed wrapper output | `c1f759c3b6e78c88c1be8388663e4e89ded1d1ec1a0fe1dc2394b6fcc435ee74` |
| Compressed wrapper output | `e14895c6ee73ea9c782c5f6bafc64c9eed28f12194f1ea84871958b87045605a` |
