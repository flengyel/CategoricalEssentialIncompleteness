# Reader two evidence

The [report](report.md) and [summary](summary.json) identify the tested commit and findings. To check the package, run `sha256sum -c SHA256SUMS` in this directory.

The blind archive contains the original manuscript-only reconstruction, including the reading-order inventory of assertions and the text of each numbered statement. Extract it in a fresh directory and run `sha256sum -c reconstruction.sha256` there. The independent digest of that checksum file is in the report.

The column `numbered_proof` in the individual assertion ledger identifies the associated record in `numbered-crosswalk.json.gz`. Its `statements` array gives each fully qualified name, real source and line, along with the source digest. The `correspondence_rows` array points to the active section dossiers and to changes in the v81 ledger. `proof-row-index.json.gz` resolves their explicit file and line references. Use the cited dossier’s description to select the applicable inference for an unnumbered statement.

The kernel archive contains the independent Lean sources, raw output, transitive axiom reports, and exact command records. Extract it in a fresh directory. With an existing project build and pinned Lean installation, run the following commands in the extracted directory using the absolute path to a checkout at the tested commit.

```sh
python3 replay-local.py --checkout /path/to/tested-checkout --mode structure
python3 replay-local.py --checkout /path/to/tested-checkout --mode numbered
python3 replay-local.py --checkout /path/to/tested-checkout --mode historical
python3 replay-local.py --checkout /path/to/tested-checkout --mode apply
```

The [external-source inventory](primary-sources.json) identifies the independently assessed published passages and the extent of source access for each entry. After the full replay receipt is published, run the following command from this verification package.

```sh
python3 confirm-receipt.py --checkout /path/to/repository --receipt /path/to/canonical-receipt.json.gz --out receipt-confirmation.json
```
