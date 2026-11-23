# WSL2 Codex — Lean proofs for manuscript v74

Work in the WSL2 checkout of flengyel/CategoricalEssentialIncompleteness. Fetch origin/main and locate the commit introducing this file. Read the current manuscript manifest, its correspondence table, and [the v73 audit of the mathematical statements](reviews/V73_MANUSCRIPT_AUDIT.md). Preserve any more recent local manuscript and unrelated changes. Complete the Lean work below on the current development and push the tested changes and report to origin/main. The author has authorized this push. Palomar v3 records manuscript v72.

## 1. Unit of the slice adjunction

The unit in Theorem 5.2 has source $Y$ and target $Y_T=T\times_U Y$. It is the partial inverse of $m:Y_T\hookrightarrow Y$. Its restriction $mm^\dagger$ is an endomorphism of $Y$. The type and proof of [right_unit_span](../Lean/CategoricalEssentialIncompleteness/V46PartialSliceSpanChangeBase.lean#L56) already give the unit correctly. Apply this documentation patch.

```diff
--- a/Lean/CategoricalEssentialIncompleteness/V46PartialSliceSpanChangeBase.lean
+++ b/Lean/CategoricalEssentialIncompleteness/V46PartialSliceSpanChangeBase.lean
@@ -51,8 +51,8 @@
     infer_instance
   exact Over.mono_of_mono_left _

-/-- The second unit is the literal partial identity whose domain is the pullback
-monomorphism, in the monic-span quotient. -/
+/-- The unit of the adjunction from reindexing to postcomposition is the partial inverse
+of the pullback inclusion. -/
 theorem right_unit_span (Y : PartialMaps.Par (Over U)) :
     (rightAdjunction i inverses).unit.app Y =
       PartialMaps.inverseMono (pullbackInclusion i inverses Y) := by
```

## 2. Infinite computably enumerable carriers in §5

Prove the final example of §5 for every infinite $A\subseteq\mathbb N$ satisfying `REPred (· ∈ A)`. Construct a total computable injection $e:\mathbb N\to\mathbb N$ with range exactly $A$ and a partial recursive inverse $r$. Prove both equations $re=1_{\mathbb N}$ and $er=1_A$, where $1_A$ is the partial identity on the ambient numerical object. Exhibit the isomorphism with the split object for $A$, then the equivalence of the partial-map slices by transport over that isomorphism.

Use the printed proof. Choose a semideciding program for $A$. Code an input $x$ together with its first halting stage $s$. This gives a recursive set $D$ of pairs, and first projection is a bijection $D\to A$. Enumerate $D$ increasingly with [computable_nth](../Lean/CategoricalEssentialIncompleteness/NumericalEnumeration.lean#L44), then project to obtain $e$. Search for the unique $n$ satisfying $e(n)=x$ to compute $r$. Increasingness is a property of the enumeration of $D$. For an arbitrary c.e. $A$, requiring an increasing computable enumeration of $A$ would imply that $A$ is recursive. The bounded evaluator and its monotonicity, soundness and completeness in pinned Mathlib support the first-stage predicate. [Carrier morphisms and extensionality](../Lean/CategoricalEssentialIncompleteness/EnumerableCarriers.lean#L212)

## 3. Two unnumbered examples

- **Appendix D, after Corollary D.2.** Prove the stated failure of the Turing property for the image of the source Turing morphism under the family functor, in the product of partial-function categories used in Theorem D.1. Choose a countable model coordinate $M$ using consistency. Put $t=F_M(\tau_T)$ in the product coordinates of the paper. At $M$ take the partial function $h$ of constant value $0^M$ with domain $\{x:(x,x)\notin\operatorname{dom}t\}$. At every other coordinate take zero. Any total parameter for this family would give $m$ with $h(x)\simeq t(m,x)$ for all $x$. Substituting $x=m$ contradicts equality of domains. Include the comparison isomorphism for the product if the presentation uses coded pairs. [Family functor](../Lean/CategoricalEssentialIncompleteness/SyntacticFamily.lean)
- **After Corollary 4.3.** For a nontrivial group $G$ with its left regular action, show in $G$-sets that $1\hookrightarrow 1+G$ is proper and every equivariant $1\to 1+G$ factors through it. This is the example separating a proper subobject from a missing global point. The categorical incompleteness theorem itself is already proved. [Corollary 4.3](../Lean/CategoricalEssentialIncompleteness/RestrictionIdempotents.lean#L222)

## 4. Identify the remaining comparisons

For §6, identify exactly which Lean equivalence has the coded object terms as its target and which argument identifies their set realizations with the chosen presentation of Montagna's category. For the unnumbered functor in §8, identify the numerical sentence coding of the existing formal functor and the comparisons with the manuscript's named syntax. Where a comparison is already proved, give its type, module and line. If a separate Lean proof is needed to identify the two objects or actions on morphisms, state and prove that comparison or record precisely what remains open. Do not replace the paper's same-language extension conditions, external use of Miller's existence theorem, or the two coding conventions with stronger claims. [Coded objects](../Lean/CategoricalEssentialIncompleteness/V46PrintedObjectCoding.lean) · [Observation functor](../Lean/CategoricalEssentialIncompleteness/ArithmeticObservationFunctor.lean)

## Checks and delivery

Integrate the new declarations into the project imports and the appropriate statement and transitive axiom audits. Independently state the conclusions with their full hypotheses in the statement checks. Run the targeted builds with warnings as errors, then run `scripts/verify-wsl.sh` from the repository root using the pinned toolchain. Record the tested commit, commands and exit codes. Keep the three Palomar theorem declarations, auxiliary definition, version-3 tag and receipt intact. No submission or registration is part of this task.

Update the v74 correspondence with the theorem names, hypotheses and whether each item is now proved. Distinguish proved comparisons from paper arguments. Commit the finished changes and report together and push to public `origin/main` without force. Fetch again, verify that the tested proof files are at the reported remote commit, and return the commit and report in the originating manuscript chat.
