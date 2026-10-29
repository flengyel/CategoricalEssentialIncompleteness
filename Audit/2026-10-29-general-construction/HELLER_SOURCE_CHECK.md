# Heller 1990: targeted source check

This is a check of the passages relevant to the supplement, not a complete
errata list for Alex Heller, *An existence theorem for recursion categories*,
JSL 55 (1990), 1252–1268.

The supplied PDF has SHA-256
`9464807984ec2949473ae83c44071d76bd32b57e2884600c01cf8536137634f2`.
Printed pp.1261, 1262, and 1267 are PDF pages 11, 12, and 17. Those pages were
rendered and inspected directly. Extracted text alone was not used to decide
whether a discrepancy occurs in print. The mathematical reviewer independently
confirmed the three substantive typing errors below.

## Printed discrepancies on p.1262

| Location | Printed formula | Typed reading and reason |
| --- | --- | --- |
| First paragraph, product equality | `Θ_X × Θ_X` compared with `Θ_(X×Y)` | The second factor must be `Θ_Y`. Under the middle-pair transposition, the domain on `(X×Y)²` comes from the equality domain on `X²` times that on `Y²`. |
| Definition of division, with `φ:W→X`, `ψ:W→Y` | `(φ×φ)*Θ_Y ⊆ (ψ×ψ)*Θ_X` | The subscripts must be `X` on the left and `Y` on the right. The codomains of `φ×φ` and `ψ×ψ` are `X²` and `Y²`, respectively. The intended relation compares the kernel equality of `φ` with that of `ψ`. |
| Proof of Proposition 6.2 | `φσ = ψ/φ` | Here `σ:X→X×Y` is a section of `p₀ ran⟨φ,ψ⟩`. The composite `φσ` is not typed. The quotient composite is `p₁σ:X→Y`; the construction gives `(p₁σ)φ=ψ`. |

The union paragraph also begins with a domain denoted `σ` and then uses `δ`
throughout its defining equations. This is a bound-symbol mismatch, resolved
by naming the union consistently. These are printed discrepancies; the PDF's
OCR introduces further corruption of symbols and subscripts.

## Effect on the present supplement

The supplement source remains
`3baa04a2cc03c2e1b50721aa9489b3687e6d7db1547f58c21cb618bbb99b3491`.
No manuscript change is required by the discrepancies above:

- **Range agreement, §6, p.1261.** The receiving and universal-agreement
  conditions are stated explicitly in the supplement. Its proofs use those
  stated equations. Heller's additional product preservation for an rP-category
  is not silently inferred from a weaker range-operator assumption.
- **Stable unions, §6, p.1262.** The supplement uses an upper domain with the
  universal-agreement property and defines stability by restriction product
  with an identity. This matches the mathematical definition in the printed
  paragraph after consistently renaming its union. The finite-stage and
  finite-product arguments are supplied in the supplement.
- **Equality filtering.** The supplement proves the needed property of
  `ran(Δ_S)` directly from universal ranges and the diagonal equations. It
  invokes neither the defective product-equality formula nor the division
  formula or Proposition 6.2.
- **Iteration.** Lemma 7.1 is not used to discharge a domain-union hypothesis.
  Constructing an evaluator from an appropriate iteration structure remains
  an open problem in this supplement. Any later use must reconstruct the
  lemma with typed maps and verify its hypotheses and proof.
- **Range counterexample, §10, Example 5, p.1267.** The citation concerns the
  generated recursion subcategory `Tur(D)`, whose domains are unions of
  connected components, and its diagonal without a range. It does not assert
  that the full ambient partial-presheaf category lacks ranges. Once the
  component-domain assertion holds, universal range agreement for the diagonal
  would force its two projections to agree on a domain containing whole
  nontrivial diagonal components, which is impossible. The supplement's
  separate selected-presheaf counterexample has its own complete proof.

This check does not establish that every printed assertion in the paper is
correct, or that correcting a formula alone proves its surrounding theorem.
Further imports from the paper require their own typing and proof checks.
