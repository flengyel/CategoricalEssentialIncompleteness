import CategoricalEssentialIncompleteness.V46FirstOrderModelSoundness

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.FirstOrderModelSoundnessChecks
open FirstOrderModelSoundness
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable {V : PredicateCategory T} {σ π : ℕ → PredicateCategory T} {d : ℕ}
variable (S : CategoricalSyntax V σ π d)
variable {A : PredicateCategory T} (axioms : A ⟶ S.sentenceObject)
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]
variable (Q : Obj T M S.algebra.a.2 → Prop)

example (h : AxiomsProperty T S axioms M Q) :
    ∀ a : Obj T M A, Q ((F T M).map (axioms ≫ S.sentenceInclusion) a) :=
  (axiomsProperty_iff T S axioms M Q).mp h

example (h : ConclusionProperty T S axioms M Q) :
    ∀ p : Obj T M (SyntacticDerivation.derivationAlgebra T (S.logicalRules axioms)).a.left,
      Q ((F T M).map (SyntacticDerivation.derivationAlgebra T (S.logicalRules axioms)).a.hom p) :=
  (conclusionProperty_iff T S axioms M Q).mp h

example (h : SentenceProperty T S axioms M Q) :
    ∃! e : Obj T M (pullback
      (SyntacticDerivation.derivationAlgebra T (S.logicalRules axioms)).a.hom S.sentenceInclusion) ⟶
      ({s : Obj T M S.sentenceObject | Q ((F T M).map S.sentenceInclusion s)} : Type),
      e ≫ validityInclusion T S M Q = (F T M).map
        (pullback.snd (SyntacticDerivation.derivationAlgebra T (S.logicalRules axioms)).a.hom
          S.sentenceInclusion) :=
  exists_unique_factor T S axioms M Q h

section Standard
variable [ℕ↓[ℒₒᵣ] ⊧* T] (Q₀ : Obj T ℕ S.algebra.a.2 → Prop)
example
    (hl : ∀ l : Obj T ℕ S.logicalParameters, Q₀ ((F T ℕ).map S.logicalAxioms l))
    (ha : AxiomsProperty T S axioms ℕ Q₀)
    (hg : ∀ z : Obj T ℕ (V ⨯ S.algebra.a.2),
      Q₀ ((F T ℕ).map (prod.snd : V ⨯ S.algebra.a.2 ⟶ S.algebra.a.2) z) →
        Q₀ ((F T ℕ).map S.quantifierConstructor z))
    (hm : ∀ z : Obj T ℕ (S.algebra.a.2 ⨯ S.algebra.a.2),
      Q₀ ((F T ℕ).map (prod.fst : S.algebra.a.2 ⨯ S.algebra.a.2 ⟶ S.algebra.a.2) z) →
      Q₀ ((F T ℕ).map S.implicationConstructor z) →
      Q₀ ((F T ℕ).map (prod.snd : S.algebra.a.2 ⨯ S.algebra.a.2 ⟶ S.algebra.a.2) z)) :
    ∀ p : Obj T ℕ (SyntacticDerivation.derivationAlgebra T (S.logicalRules axioms)).a.left,
      Q₀ ((F T ℕ).map (SyntacticDerivation.derivationAlgebra T (S.logicalRules axioms)).a.hom p) :=
  (conclusionProperty_iff T S axioms ℕ Q₀).mp (conclusion_property T S axioms Q₀ hl ha hg hm)
end Standard

end CategoricalEssentialIncompleteness.V46.FirstOrderModelSoundnessChecks
