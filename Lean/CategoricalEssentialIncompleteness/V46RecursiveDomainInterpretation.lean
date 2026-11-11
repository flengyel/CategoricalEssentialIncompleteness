/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46PredicateInterpretationDomain

/-! # Domain interpretation on recursively interpreted object carriers -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment CategoryTheory
open FailureOfComposition.TypedProgramCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.PredicateInterpretation

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]

/-- The existing coding comparison preserves the entire interpreted
partial graph, including its domain. -/
theorem mem_recursive_model {Q R : FailureOfComposition.TypedProgramCategory.CodedProgramCategory T}
    (f : Q ⟶ R) (x : SyntacticModel.interpretedType M (objectCode Q))
    (y : SyntacticModel.interpretedType M (objectCode R)) :
    y ∈ (SyntacticModel.modelFunctor T M).map f x ↔
      SyntacticModel.codingEquiv T M (objectCode R) y ∈
        SyntacticModel.arrow T M f (SyntacticModel.codingEquiv T M (objectCode Q) x) :=
  PartialFunctions.mem_conjugate (SyntacticModel.codingEquiv T M (objectCode Q))
    (SyntacticModel.codingEquiv T M (objectCode R)) (SyntacticModel.arrow T M f) x y

/-- Literal domains of interpreted idempotents on the manuscript's
recursively interpreted product and coproduct carriers. -/
abbrev RecursiveDomain (X : TotalSplit T) : Type :=
  {x : SyntacticModel.interpretedType M (objectCode X.obj.base) //
    x ∈ (SyntacticModel.modelFunctor T M).map X.obj.domain.hom x}

def recursiveDomainEquiv (X : TotalSplit T) :
    RecursiveDomain T M X ≃ CanonicalDomain T M X :=
  Equiv.subtypeEquiv (SyntacticModel.codingEquiv T M (objectCode X.obj.base))
    (fun x => mem_recursive_model T M X.obj.domain.hom x x)

def recursiveDomainIso (X : TotalSplit T) :
    RecursiveDomain T M X ≅ (canonicalDomainFunctor T M).obj X :=
  (recursiveDomainEquiv T M X).toIso

/-- The chosen-domain interpretation with the original recursively
interpreted carriers. Morphisms are the restrictions of F_M(f). -/
def recursiveDomainFunctor : TotalSplit T ⥤ Type where
  obj X := RecursiveDomain T M X
  map {X Y} f := (recursiveDomainIso T M X).hom ≫
    (canonicalDomainFunctor T M).map f ≫ (recursiveDomainIso T M Y).inv
  map_id X := by
    rw [(canonicalDomainFunctor T M).map_id X, Category.id_comp, Iso.hom_inv_id]
  map_comp f g := by
    simp only [Functor.map_comp, Category.assoc]
    rw [← Category.assoc (recursiveDomainIso T M _).inv,
      Iso.inv_hom_id, Category.id_comp]

/-- The existing gamma coding lifts naturally through all chosen
idempotent domains, not merely through included source objects. -/
def recursiveDomainComparison : recursiveDomainFunctor T M ≅ canonicalDomainFunctor T M :=
  NatIso.ofComponents (recursiveDomainIso T M) (by
    intro X Y f
    simp only [recursiveDomainFunctor, Category.assoc, Iso.inv_hom_id, Category.comp_id])

/-- Every total-split morphism is interpreted by exactly the original
partial model graph restricted to its two domain carriers. -/
theorem recursiveDomainFunctor_graph {X Y : TotalSplit T} (f : X ⟶ Y)
    (x : RecursiveDomain T M X) (y : RecursiveDomain T M Y) :
    (recursiveDomainFunctor T M).map f x = y ↔
      y.val ∈ (SyntacticModel.modelFunctor T M).map f.hom.hom x.val := by
  change (recursiveDomainEquiv T M Y).symm
      ((canonicalDomainFunctor T M).map f (recursiveDomainEquiv T M X x)) = y ↔ _
  rw [Equiv.symm_apply_eq, canonicalDomainFunctor_graph, mem_recursive_model,
    SyntacticModel.mem_arrow]
  rfl

end CategoricalEssentialIncompleteness.V46.PredicateInterpretation
