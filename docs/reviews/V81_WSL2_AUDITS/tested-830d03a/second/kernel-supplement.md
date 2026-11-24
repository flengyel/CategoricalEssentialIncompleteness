# Independent second-reader Lean checks for v81

At `830d03a5adcf144a003feb36f88bd06e0c5b0cf5`, I ran **24 successful strict Lean invocations**. They elaborate the two independently reconstructed proposition vocabularies, prove seven applications at actual manuscript types, and print the full types and transitive axioms of **189 distinct declarations across all 80 numbered items**. Together with the [numbered source comparison](numbered-comparison.md), these are this reader's direct checks on the frozen proof sources. Their scope is separate from the [official full replay](../../../../V81_WSL2_LEAN_VERIFICATION.json.gz). [Inputs, outputs, per-process results, hashes and declaration map](kernel-supplement.json.gz)

I used the pinned Lean `4.35.0-rc2` in a separate scratch process, reading the candidate's compiled imports. Each invocation used one thread and treated warnings as errors. The 21 successful batches of numbered declarations used exact source names, with each statement checked by Lean and each transitive axiom list printed. Four declarations use no axioms, three use `propext` alone, one uses `propext` and `Classical.choice`, one uses `propext` and `Quot.sound`, and 180 use all three. The largest measured resident set among the successful runs was 1,858,180 KiB. The official wrapper retained its own build lock and outputs throughout. [Bundle with exact source and log bytes](kernel-supplement.json.gz)

The seven applications check the following obligations.

| Native statement | Independent proof |
|---|---|
| From a P-category obtain the binary restriction products on the given induced restriction | Constructs the product, total projections and pairing, then applies the two projection equations, the restriction equation and uniqueness by projections. This supplies one direction of Cockett–Lack III 4.5. |
| Numerical inseparability of nonempty disjoint saturated unions | Takes a precomplete numerical relation and both saturated sets, with no computable enumerations of those sets. |
| Existence of a Miller sequence | Obtains one point `a` before quantifying over program indices and real values, with every binary name of `a` and every precision in the antecedent. |
| Di Paola–Heller counterexample | Exhibits the sum-valued Turing morphism in the one-object category, the equality of identity and zero and the failure of inseparability. |
| Voutsadakis’ adjunction | Constructs the term of the adjunction type for the native free-signature and formula-valued functors. |
| Murwanashyaka–Pakhomov–Visser | For any disjoint c.e. pair, obtains consistency and the biconditional with essential undecidability in the actual first-order class-size theory. |
| Uniform PA independence | Extracts a morphism in the arithmetic total category before choosing the theory index. The sentence it computes is closed and neither sign is derivable by the finite named rules. |

The original blind specifications remain sealed. In each, I wrote two structure projections on a single line. Lean interpreted the second name as a binder of the first projection. The elaborated copies declare `zero` and `top`, or `prod` and `sum`, on separate lines. To stay inside the memory allowance I also replaced `import Mathlib` in the main specification with the adjunction and real-number imports it uses. An automated comparison verifies these exact edits and no change to any proposition body. The aggregate import in the untouched original exceeded the scratch memory cutoff. An additional attempt using just the narrower imports confirmed the original projection error. The bundle preserves those attempts and all successful reruns. [Original blind seal](blind-seal.sha256) · [machine bundle](kernel-supplement.json.gz)

The independent source verdict and reconciliation retain their original scope and hashes. This extra evidence certifies the typed comparisons and applications listed here. The fifteen outstanding original historical conclusions and the false unrestricted Di Paola–Heller conclusion remain recorded in the [signed reconciliation](reconciliation.md). Signed by **Codex, independent second reader**.
