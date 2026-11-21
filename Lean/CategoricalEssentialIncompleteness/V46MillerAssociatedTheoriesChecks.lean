/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46MillerAssociatedTheories

/-! # Independent checks of Miller extension domains and the common theorem -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46 Miller AssociatedData AssociatedTheories
variable (a : Point)

example : IsTerminal (pointDomain a) := pointDomain_terminal a

example (U : Theory a) :
    ∃ p : pointDomain a ⟶ (U.val : Total.CanonicalTotal a),
      p ≫ U.val.arrow = theoremPoint a := point_factors a U

example : logicalPoint a ≫ (syntaxData a).logicalAxioms =
    theoremPoint a ≫ (syntaxData a).sentenceInclusion := logicalPoint_diagram a

example (A : Subobject (syntaxData a).sentenceObject) : IsInitial (proofs a A) := initial a A

example (U : Theory a) :
    CanonicalAxiomIncompleteness.theoremIdem a U.val.arrow =
      RestrictionSubobjects.domain (inverses a) U.val := theory_domain a U

example (U : Theory a) :
    CanonicalAxiomIncompleteness.refutationIdem a U.val.arrow =
      RestrictionSubobjects.domain (inverses a)
        ((Subobject.pullback (syntaxData a).sentenceNegation).obj U.val) := refutation_domain a U

/-- The extension is any closed internal theory, with the Miller assumption and
generated-image inclusion and consistency equation. -/
example (ha : IsMiller a) (U : Theory a) (hExt : base a ≤ U.val)
    (hc : U.val ⊓ (Subobject.pullback (syntaxData a).sentenceNegation).obj U.val = ⊥) :
    SubobjectInseparable U.val ((Subobject.pullback (syntaxData a).sentenceNegation).obj U.val) ∧
      U.val ⊔ (Subobject.pullback (syntaxData a).sentenceNegation).obj U.val ≠ ⊤ :=
  global_incompleteness a ha U hExt hc

#print axioms RestrictionSubobjects.inverse_eq_span
#print axioms RestrictionSubobjects.domain_eq_range
#print axioms RestrictionSubobjects.domain_pullback
#print axioms RestrictionSubobjects.domain_image
#print axioms AssociatedData.proofs
#print axioms AssociatedData.initial
#print axioms AssociatedData.pointDomain_terminal
#print axioms AssociatedData.sourceDiagram
#print axioms AssociatedData.logicalPoint_diagram
#print axioms AssociatedData.point_factors
#print axioms AssociatedTheories.generated_domain
#print axioms AssociatedTheories.theory_domain
#print axioms AssociatedTheories.refutation_domain
#print axioms AssociatedTheories.base_domain
#print axioms AssociatedTheories.global_incompleteness
