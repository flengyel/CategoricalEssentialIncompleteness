# Independent statement checks and kernel evidence

The tested source is `98f8d0d50a0cc08885d07ab4d71ec6f6a7adf885`. I ran strict Lean elaboration for the 852 distinct declarations in the current correspondence for 80 numbered items. Eighteen batches completed with exit code 0. I matched each displayed type to the exact requested fully qualified name, and every numbered row retains its defining source. The five new propositions below also completed with exit code 0. They use the checkout’s populated, pinned Lean cache. Their successful elaboration supplements the official full replay. [Full elaborated types](numbered-types.txt.gz) · [Commands, exit codes and output digests](commands.json) · [Replay sources and five proof logs](reader-probes.tar.gz)

| Independent proposition | Checked claim |
|---|---|
| `FirstReading.separator_and_closed_extensions` | For any disjoint pair whose signed theory is consistent, subobject inseparability is equivalent to failure of the explicit cover equation for **every** internally closed consistent extension. |
| `FirstReading.indexed_miller_witness` | There exists one real sequence. For every program and interval real, the uniform strict approximation implication holds on all binary names and precisions for the literal evaluator and rational enumeration. |
| `FirstReading.discrete_exception` | The chosen morphism in the one-morphism dominical category is Turing, and the preimages of its two summand domains have a separator. |
| `FirstReading.consistent_presentation_without_independent_sentence` | Some consistent theory has decidable axiom codes and decides, with respect to the indicated calculus, every sentence of its fixed language. |
| `FirstReading.one_sentence_morphism` | There exists one PA sentence morphism, chosen before the index, whose standard value codes a closed formula with neither a positive nor a negative derivation whenever the indexed extension is consistent. |

The one-morphism exception uses `propext`. Each of the other four proofs uses only `propext`, `Classical.choice` and `Quot.sound`. To repeat the reader checks, unpack the archive into a scratch directory inside a checkout of the tested commit that has the project’s compiled dependencies, and run the following commands from that directory. They write logs and generated probe sources inside the scratch directory.

```bash
bash run-independent.sh
python3 probe-numbered.py run
```

For the official check, `scripts/verify-wsl.sh` records the starting Git commit and diff, and preserves the `scripts/verify.py` JSON and its individual command logs. The reader’s confirmation uses the original files and the final public gzip. It rematches all integration hashes to immutable Git blobs, compares each official log digest, reconstructs both axiom dictionaries independently from raw Lean output, checks every dependency pin, and matches the strict module set against the tested Git tree. Passing the targeted-log directory also checks every targeted log digest. The confirmation requires a finished wrapper with exit code 0. Its JSON identifies the original official JSON SHA-256 and the SHA-256 of the public gzip bytes. [Read-only confirmation script](confirm-receipt.py) · [Official verification report](../../../../V81_WSL2_LEAN_VERIFICATION.md) · [Official machine-readable receipt](../../../../V81_WSL2_LEAN_VERIFICATION.json.gz)

```bash
python3 confirm-receipt.py "$public_gzip" "$completed_wrapper_directory" \
  --repo "$repository_checkout" --targeted "$targeted_log_directory"
```

The reader checks certify the displayed types and the five applications above. The official transitive audit covers the declarations and modules that it names. The eight missing historical constructions in the signed source verdict have no Lean declarations that a replay can certify. [Sealed mathematical findings](source-verdict.md) · [Comparison with the second reader](reconciliation.md)
