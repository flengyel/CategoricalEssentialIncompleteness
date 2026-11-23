# v81. Remaining comparisons in §§6–7 and Appendix D

**Lemma 6.4 is proved at arbitrary unary entry formula; the printed selector is an immediate instance with the supplied binary graph.** The existing selector-specific declaration specializes to a chosen graph. The exact printed-graph application has no separate checked declaration in the files inspected. The three other qualifications concerning literal realization, the external source non-local-connectedness theorem, and the strict final category isomorphism remain distinct. Revision `986dee4d54d202a452009146cc29d19a544b0000`; source review only. Lean basenames below are under `Lean/CategoricalEssentialIncompleteness/`.

## Finite selector with its graph supplied

`manuscript/latex/sections/05a-internal-syntax.tex:291–322` fixes a positive standard integer $s$, a family $D:\mathrm{Fin}(s)\to\Sigma_1(1)$, and a specified binary graph $L(x,w)$. Define a unary condition by substituting the numeral for each external index $j$ into the **second** argument of $L$, conjoining with the given $D_j(x)$, and taking the finite disjunction. For every model $M\models\mathrm{PA}$ and every internal list code $a\in M$, the resulting witness-list formula says:

$$
  \forall i<\operatorname{len}(a)\;\exists j:\mathrm{Fin}(s),\quad
  L^M(a_i,\bar j)\land D_j^M(a_i).
$$

Here $i$ ranges over the model and $j$ ranges over the externally fixed finite list. The direct universally closed equivalence has a PA proof. The formula construction proves the guarded conclusion for *every* binary Σ₁ formula, including a graph with no numeral from that list on some input. Functional, total and internally bounded output are needed only to interpret it as an everywhere-defined unguarded choice of a single branch. Positive $s$ is the manuscript hypothesis; for $s=0$ the disjunction is false and the list condition accepts exactly empty lists.

The following are **candidate applications**, not newly compiled declarations. They use the conventions of `V46FiniteSigmaOne.lean`. The graph in the displayed manuscript is input first. The program graph in `V46PrimitiveRecursiveTags.lean:304–310,378–385` is output first: pass its transposition if it is the supplied graph.

```lean
def guardAt (L : 𝚺₁.Semisentence 2) (j : ℕ) : Carrier := .mkSigma
  “x. !L.val x !!(numeralTerm j)”

def guardedEntry {s : ℕ} (L : 𝚺₁.Semisentence 2)
    (D : Fin s → Carrier) : Carrier :=
  .mkSigma (Finset.udisj (fun j : Fin s =>
    (guardAt L j.val).val ⋏ (D j).val)) (by
      simp only [Hierarchy.finset_udisj_iff, Hierarchy.and_iff]
      intro j
      exact ⟨(guardAt L j.val).sigma_prop, (D j).sigma_prop⟩)

example {s : ℕ} (L : 𝚺₁.Semisentence 2) (D : Fin s → Carrier) :
    𝗣𝗔 ⊢ finiteMembershipSentence (guardedEntry L D) :=
  finite_membership_PA (guardedEntry L D)

example {s : ℕ} (L : 𝚺₁.Semisentence 2) (D : Fin s → Carrier)
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (a : M) :
    (finiteMembership (guardedEntry L D)).val.Evalb ![a] ↔
      ∀ i < len a, ∃ j : Fin s,
        L.val.Evalb ![nth a i, ORingStructure.numeral j.val] ∧
          (D j).val.Evalb ![nth a i] := by
  rw [← finite_membership_model, allEntriesCondition_eval]
  simp [guardedEntry, guardAt, numeralTerm]
```

`V46FiniteSigmaOne.lean:88–99,105–107,146–175,212–213` gives the list formula, internal semantics, universally quantified PA theorem, and numeral substitution term. `V46FiniteSigmaOneChecks.lean:23` explicitly checks that any unary Σ₁ formula may be passed. `V46PrimitiveRecursiveTags.lean:404–417,419–437` uses exactly the finite-disjunction hierarchy proof and the all-model list rewrite displayed above for its particular graph. Its premise is `hf : Nat.Primrec f`; `codeFor_spec` (330–333) identifies the chosen code with $f$ only on standard naturals. The checks at `V46PrimitiveRecursiveTagsChecks.lean:58–69` explicitly retain `codeFor hf`. The other disjunction at `V46FiniteSigmaOne.lean:299–327` reads a pair's first coordinate as tag and applies the condition to the payload. Its general implication construction at lines 181–209 would accept an entry when none of its tags holds.

**Counterexample to replacing the supplied graph.** Assuming consistency of PA, compare the constant-zero program and the bit-valued primitive-recursive program testing whether its input is a PA proof of contradiction. Their functions on ℕ agree. PA proves that each program returns a unique bit. By Gödel's second incompleteness theorem and completeness, there is a model of PA believing it has a proof $p$ of contradiction. Take $D_0=\top,D_1=\bot$. The one-entry list $[p]$ passes the first program's guard and fails the second's. Thus even PA-provable boundedness of both selectors cannot identify their internal graphs. With $s=1$, the same second program gives the separate obstruction that standard range $\subseteq\{0\}$ alone does not yield internal range $\subseteq\{0\}$. Nothing in the guarded lemma asserts otherwise. The parser and derivation conclusions have independent displayed initiality declarations (`V46SyntacticSyntaxInitial.lean:28,34,41`, `V46SyntacticListsInitial.lean:54`, `V46SyntacticDerivationInitial.lean:52–74,112–124`).

## Other qualifications in the interval inventory

| Passage | Precise application and status |
|---|---|
| Theorem 6.9, final c.e. axiom-code specialization | For $G\subseteq\mathbb{N}$ and `hG : REPred (· ∈ G)`, take `.mkSigma (codeOfREPred (fun n : ℕ => n ∈ G)) (by simp [codeOfREPred, codeOfPartrec'])`. Its evaluation at every standard $n$ is exactly membership by `codeOfREPred_spec hG`. This general API is used on explicit predicates in `V46NumericalCoordinatesCoding.lean:21–27` and `V46MillerFiniteAxiomProofs.lean:35–41`. Apply `V46SyntacticAxiomPredicates.lean:29–57,80–93,124` to this unary formula, intersecting it with sentencehood as specified. The input c.e. set determines the standard instances. It does not identify two formulas at nonstandard inputs. |
| Corollary 7.3, corollary for consistent $T$ | `V46SyntacticComparison.lean:49–57` takes consistency and arbitrary Turing morphism and isomorphism. This is a direct statement. The single-model version at line 32 has separate model data. |
| Theorem 7.9, equation of restriction idempotents (TeX lines 483–488) | `V46NamedPlainUltrapowerSoundness.lean:106–126,131–148` establishes the actual conclusion-image disjointness with the inverse image by the actual sentence negation. `V46PredicateInterpretationRegular.lean:290,319,331` identifies the canonical image, and `V46RecursiveDomainInterpretation.lean:70,77` compares the two interpretations. `V46LogicalComparison.lean:92` identifies interpreted theorem idempotents using the range splitting. In the partial-function target, apply `PartialFunctions.support_injective` (146), `support_inf` (209), `support_bot` (217), and `support_pull` (223). For total negation the last expression reduces to inverse image under the underlying function. `Set.disjoint_iff_inter_eq_empty` gives the support equality. The final displayed idempotent equation is thus a specialization and transport. |
| D.1, identity on an arbitrary term, lines 56–58 | The theorem states the omega case, proved at `SyntacticFamily.lean:94–101`. To obtain the proof's stronger sentence for $X$, choose $s:\mathrm{ModelIndex}(T)$ by `CountableArithmeticModels.lean:114`, then a member $x:\mathrm{interpretedType}(\mathbb{N},X)$ recursively from 0, ordered pairs, and left injections (`SyntacticModel.lean:310–314`). Evaluate the proposed identity–zero equality twice, at $s,x$; it gives `Part.some x = Part.none` exactly as in the proof at lines 96–101. Family evaluation is `SyntacticFamily.lean:33–41`. |
| D, extension inclusion of observations, lines 150–179 | Let $Q=\mathtt{SyntacticExtension.functor}\ T\ T'$. Given `h : n ∈ observation T c`, unfold `SyntacticObservations.lean:41–42`: `kappa T n ≫ c.hom = kappa T n`. Apply `congrArg Q.map h`, rewrite `Q.map_comp`, and rewrite `Q.map (kappa T n) = kappa T' n` by `SyntacticExtension.map_index T T' .omega .omega (UniformRange.rangeConstantIndex n)` (lines 50–54, with `kappa` at `SyntacticObservations.lean:28–29`). By `RangeFunctor.mapIdem_hom:62–63`, this is exactly membership in `observation T' ((SyntacticExtension.rangeFunctor T T').mapIdem c)`. The proof uses only `[𝗣𝗔 ⪯ T] [𝗣𝗔 ⪯ T'] [T ⪯ T']`; c.e. is for enumerability, consistency for bottom. `ArithmeticObservationFunctor.observations_mono:56` concerns its fixed sentence family and is insufficient on its own for arbitrary $c$. |
| D, strict common-object comparison, lines 183–200 | `StandardTrueTheory.lean:59–90` supplies the represented-map comparison, functor laws, fullness, faithfulness, and an object preimage with `Iso.refl` for every target label. An explicit inverse takes the same label and the inverse hom bijection. Its laws follow from faithfulness and the original functor laws. Strict inverse functor equations require assembling these choices at the actual labels. The cited declaration bundles an equivalence. |

No additional substantive missing premise was found in the audited rows beyond the already recorded literal set realization, the external DPM non-local-connectedness theorem, and the final strict-isomorphism assembly. For the selector, the exact correspondence check should use the supplied graph as above. It does not require proving any new PA collection theorem. The observations inclusion, stronger all-object sentence in D.1, and §7.9 support equation are explicit consequences; the source review does not claim a new kernel receipt for these applications.
