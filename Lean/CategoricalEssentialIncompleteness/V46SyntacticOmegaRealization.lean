import CategoricalEssentialIncompleteness.V46ArithmeticOmegaComparison
import CategoricalEssentialIncompleteness.V46PredicateInterpretationDomain
/-! Realization of total numerical predicate morphisms on the identity
omega splitting, with source-morphism and model-graph comparisons. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.RestrictionCategory
open FailureOfComposition FailureOfComposition.TypedProgramCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.SyntacticOmegaRealization
open NamedArithmeticSignature
section Omega
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
private def omegaWithIdem (e : Idem (omegaObject T)) : TotalSplit T := ⟨⟨omegaObject T,e⟩⟩
private theorem idem_eq_underlying {e e' : Idem (omegaObject T)} (h : e = e') :
    (eqToHom (congrArg (omegaWithIdem T) h)).hom.hom = e.hom := by
  cases h
  rfl

theorem omegaIso_underlying :
    (ArithmeticOmegaComparison.omegaIso T).hom.hom.hom = 𝟙 (omegaObject T) := by
  change (eqToHom (congrArg (omegaWithIdem T)
    (ArithmeticOmegaComparison.variables_idempotent T).symm)).hom.hom =
      (⊤ : Idem (omegaObject T)).hom
  exact idem_eq_underlying T (ArithmeticOmegaComparison.variables_idempotent T).symm

theorem map_from_omega_underlying {C : PredicateCategory T}
    (f : GraphMorphism T variableSymbols C) :
    ((ArithmeticOmegaComparison.omegaIso T).hom ≫
      (realization T).map (classOfGraph T f)).hom.hom = f.toTotal.hom.hom := by
  change (ArithmeticOmegaComparison.omegaIso T).hom.hom.hom ≫ f.toTotal.hom.hom = _
  erw [omegaIso_underlying,Category.id_comp]

variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]
def omegaDomainPoint (n : M) : PredicateInterpretation.Domain T M (ArithmeticOmegaComparison.identityOmega T) := by
  refine ⟨n,?_⟩
  change SyntacticModel.programRelation T M (⊤ : Idem (omegaObject T)).hom.val n n
  rw [← ArithmeticOmegaComparison.variables_idempotent T]
  exact (predicateClass_model T variableSymbols M n n).mpr ⟨variables_eval n,rfl⟩

def omegaPoint (n : M) : PredicateInterpretation.CanonicalDomain T M (ArithmeticOmegaComparison.identityOmega T) :=
  PredicateInterpretation.canonicalDomainEquiv T M _ (omegaDomainPoint T M n)

theorem omegaPoint_value (n : M) : (omegaPoint T M n).val.val = n := rfl
end Omega
section Realization
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
def realizeFromOmega {C : PredicateCategory T} (f : GraphMorphism T variableSymbols C) :
    ArithmeticOmegaComparison.identityOmega T ⟶ (realization T).obj C :=
  (ArithmeticOmegaComparison.omegaIso T).hom ≫ (realization T).map (classOfGraph T f)

theorem realizeFromOmega_underlying {C : PredicateCategory T} (f : GraphMorphism T variableSymbols C) :
    (realizeFromOmega T f).hom.hom = f.toTotal.hom.hom :=
  map_from_omega_underlying T f

theorem realizeFromOmega_graph {C : PredicateCategory T} (f : GraphMorphism T variableSymbols C)
    (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]
    (x : PredicateInterpretation.CanonicalDomain T M (ArithmeticOmegaComparison.identityOmega T))
    (y : PredicateInterpretation.CanonicalDomain T M ((realization T).obj C)) :
    (PredicateInterpretation.canonicalDomainFunctor T M).map (realizeFromOmega T f) x = y ↔
      f.graph.val.Evalb ![x.val.val,y.val.val] := by
  erw [PredicateInterpretation.canonicalDomainFunctor_graph,realizeFromOmega_underlying]
  exact f.programClass_model M _ _
end Realization

end CategoricalEssentialIncompleteness.V46.SyntacticOmegaRealization
