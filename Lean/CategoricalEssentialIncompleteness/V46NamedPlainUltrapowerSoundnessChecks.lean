import CategoricalEssentialIncompleteness.V46NamedPlainUltrapowerSoundness

noncomputable section
universe w
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits Filter
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.NamedPlainUltrapowerSoundnessChecks
open SyntacticSyntax NamedPostfixEncoding NamedPlainSemantics SyntacticGeneratedTheory
variable (σ π : ℕ → PredicateCategory 𝗣𝗔) (d : ℕ)
local notation "S" => plainCategoricalSyntax 𝗣𝗔 (variableCarrier : PredicateCategory 𝗣𝗔) σ π d
local notation "G" => F 𝗣𝗔 ℕ
local notation "E" => realization 𝗣𝗔
variable {K : Type w} [Nonempty K]
  (functions : ∀ n : Fin (d + 1), Symbols σ n.val → (Fin n.val → K) → K)
  (relations : ∀ n : Fin (d + 1), Symbols π n.val → (Fin n.val → K) → Prop)
variable {A : PredicateCategory 𝗣𝗔} (axioms : Hom 𝗣𝗔 A
  (CategoricalSyntax.sentenceObject
    (plainCategoricalSyntax 𝗣𝗔 (variableCarrier : PredicateCategory 𝗣𝗔) σ π d)))
variable (haxioms : FirstOrderModelSoundness.AxiomsProperty 𝗣𝗔
  (V := (variableCarrier : PredicateCategory 𝗣𝗔)) (σ := σ) (π := π) (d := d)
  (plainCategoricalSyntax 𝗣𝗔 (variableCarrier : PredicateCategory 𝗣𝗔) σ π d)
  (A := A) axioms ℕ (Valid σ π d functions relations))
example {I : Type} (U : Ultrafilter I) :
    Mono (Ultrapower.transportValidity U (ArithmeticUltrapower.canonicalComparison U)
      (canonicalValidityInclusion σ π d functions relations)) ∧
    Ultrapower.transportSoundness U (ArithmeticUltrapower.canonicalComparison U)
        (canonicalSoundnessFactor σ π d functions relations (A := A) axioms haxioms) ≫
      Ultrapower.transportValidity U (ArithmeticUltrapower.canonicalComparison U)
        (canonicalValidityInclusion σ π d functions relations) =
      (PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔 (ArithmeticUltrapower.Model U)).map
        ((E).map (FirstOrderModelSoundness.sentenceConclusion 𝗣𝗔 (V := (variableCarrier : PredicateCategory 𝗣𝗔)) (σ := σ) (π := π) (d := d) (S) (A := A) axioms)) ∧
    Disjoint (Set.range (Ultrapower.transportValidity U (ArithmeticUltrapower.canonicalComparison U)
      (canonicalValidityInclusion σ π d functions relations)))
      (((PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔 (ArithmeticUltrapower.Model U)).map
          ((E).map (S).sentenceNegation)) ⁻¹'
        Set.range (Ultrapower.transportValidity U (ArithmeticUltrapower.canonicalComparison U)
          (canonicalValidityInclusion σ π d functions relations))) :=
  canonical_ultrapower_soundness σ π d functions relations (A := A) axioms haxioms U
example {I : Type} (U : Ultrafilter I) :
    Disjoint
      (Set.range ((PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔
        (ArithmeticUltrapower.Model U)).map
          ((E).map (FirstOrderModelSoundness.sentenceConclusion 𝗣𝗔 (V := (variableCarrier : PredicateCategory 𝗣𝗔)) (σ := σ) (π := π) (d := d) (S) (A := A) axioms))))
      (((PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔
          (ArithmeticUltrapower.Model U)).map ((E).map (S).sentenceNegation)) ⁻¹'
        Set.range ((PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔
          (ArithmeticUltrapower.Model U)).map
            ((E).map (FirstOrderModelSoundness.sentenceConclusion 𝗣𝗔 (V := (variableCarrier : PredicateCategory 𝗣𝗔)) (σ := σ) (π := π) (d := d) (S) (A := A) axioms)))) :=
  canonical_ultrapower_conclusion_consistent σ π d functions relations (A := A) axioms haxioms U
end CategoricalEssentialIncompleteness.V46.NamedPlainUltrapowerSoundnessChecks
