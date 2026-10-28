/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.EnrichedDomains
import CategoricalEssentialIncompleteness.BooleanPresentations

/-!
# Boolean quotient incompleteness from the enriched representation section

The separator obstruction now uses the actual domain equalizers and totality
pullbacks. Only the sentence-object component of the subobject identification
is used in this argument. Packaging that component from the full global
comparison along `J` remains a separate construction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe v u w v' u'
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness
namespace EnrichedRestriction
variable {V : Type u} [Category.{v} V] [HasFiniteLimits V] {O : Type w}
variable {H : InternalHom V O} (R : EnrichedRestriction H) [R.Zeros] [R.DomainLattices]
variable (products : R.Products) {P : InternalPredicates (R.totalHom products)}
variable (D : InternalDiagonalData (R.domainPredicates products) P)
variable (σ : D.RepresentationSection) (hU : H.unit D.U ≠ Zeros.zero R D.U D.U)
variable {C : Type u'} [Category.{v'} C] [Regular C] [FinitaryExtensive C] {X : C}
variable (identify : (⊤_ V ⟶ (P.lattice D.S).obj) ≃o Subobject X)
variable (q : BooleanPresentation X)
variable (hpos : identify D.positive = q.positive) (hneg : identify D.negative = q.negative)
variable (r : BooleanQuotient q.algebra) (a b : ⊤_ V ⟶ R.domainObject D.S)
variable (ha : identify (a ≫ (D.embedding.app D.S).hom) = (q.quotient r).positive)
variable (hb : identify (b ≫ (D.embedding.app D.S).hom) = (q.quotient r).negative)

include σ hU hpos hneg ha hb

/-- Consistent represented Boolean quotients are incomplete, with representation
obtained from the internal section. The identification is explicit at `S`. -/
theorem enriched_boolean_quotient_incomplete (consistent : (q.quotient r).Consistent) :
    ¬ (q.quotient r).Complete := by
  intro complete
  have hp : D.positive ≤ a ≫ (D.embedding.app D.S).hom := by
    apply identify.le_iff_le.mp
    rw [hpos, ha]
    exact boundFiber_le_postcomp q.q r.morphism.hom ⊤ ⊤ (r.morphism.preserves_top _)
  have hn : D.negative ≤ b ≫ (D.embedding.app D.S).hom := by
    apply identify.le_iff_le.mp
    rw [hneg, hb]
    exact boundFiber_le_postcomp q.q r.morphism.hom ⊥ ⊥ (r.morphism.preserves_bot _)
  have hmeet : a ⊓ b = ⊥ := by
    apply D.embedding.injective (⊤_ V) D.S
    apply identify.injective
    simpa only [BooleanPresentation.Consistent, map_inf, map_bot,
      InternalLatticeHom.postcomp_apply, ha, hb] using consistent
  have hjoin : a ⊔ b = ⊤ := by
    apply D.embedding.injective (⊤_ V) D.S
    apply identify.injective
    simpa only [BooleanPresentation.Complete, map_sup, map_top,
      InternalLatticeHom.postcomp_apply, ha, hb] using complete
  let pair : ComplementaryPair (⊤_ V ⟶ R.domainObject D.S) :=
    ⟨a, b, IsCompl.of_eq hmeet hjoin⟩
  have hsep : D.Separates pair := by
    simpa only [InternalDiagonalData.Separates, pair, InternalDiagonalData.positiveAt,
      InternalDiagonalData.negativeAt, InternalLatticeHom.postcomp_apply,
      terminalIsTerminal.hom_ext (terminal.from (⊤_ V)) (𝟙 (⊤_ V)), Category.id_comp]
      using And.intro hp hn
  exact (R.enriched_no_global_separator products D σ hU).false (D.liftSeparator pair hsep)

/-- The equivalent conclusion about the genuine Boolean bound copairing. -/
theorem enriched_boundCopair_not_regularEpi (consistent : (q.quotient r).Consistent) :
    ¬ IsRegularEpi r.target.boundCopair := by
  intro h
  exact R.enriched_boolean_quotient_incomplete products D σ hU identify q hpos hneg r a b ha hb
    consistent ((q.quotient r).complete_iff_regularEpi.mpr h)

end EnrichedRestriction
end CategoricalEssentialIncompleteness
