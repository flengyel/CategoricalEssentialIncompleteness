/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46RecursiveDomainInterpretation
public import CategoricalEssentialIncompleteness.V46PredicateInterpretationRegular

/-! # Regularity on the manuscript's recursively interpreted domain carriers -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.PredicateInterpretation

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]

instance recursivePreservesFiniteLimits : PreservesFiniteLimits (recursiveDomainFunctor T M) :=
  preservesFiniteLimits_of_natIso (recursiveDomainComparison T M).symm

instance recursivePreservesFiniteCoproducts :
    PreservesFiniteCoproducts (recursiveDomainFunctor T M) where
  preserves _n := preservesColimitsOfShape_of_natIso (recursiveDomainComparison T M).symm

private theorem recursive_map_conjugate {A : Type*} [Category A] {G H : A ⥤ Type}
    (η : G ≅ H) {X Y : A} (f : X ⟶ Y) :
    H.map f = η.inv.app X ≫ G.map f ≫ η.hom.app Y := by
  symm
  rw [η.hom.naturality, ← Category.assoc, η.inv_hom_id_app, Category.id_comp]

/-- The image comparison for the recursive-domain interpretation is over
the actual recursively interpreted codomain, for every total-split morphism. -/
theorem preserves_recursive_regularImage {X Y : TotalSplit T} (f : X ⟶ Y) :
    ∃ e : (recursiveDomainFunctor T M).obj (image f) ≅
      image ((recursiveDomainFunctor T M).map f),
      e.hom ≫ image.ι ((recursiveDomainFunctor T M).map f) =
        (recursiveDomainFunctor T M).map (image.ι f) := by
  let G := canonicalDomainFunctor T M
  let H := recursiveDomainFunctor T M
  let η := (recursiveDomainComparison T M).symm
  let i := canonicalRegularImageIso T M f
  have hleft : G.map (factorThruImage f) ≫ i.hom = factorThruImage (G.map f) := by
    apply (cancel_mono (image.ι (G.map f))).mp
    rw [Category.assoc, canonicalRegularImageIso_hom_ι, ← G.map_comp, image.fac, image.fac]
  have he : G.map (factorThruImage f) = factorThruImage (G.map f) ≫ i.inv := by
    rw [← hleft, Category.assoc, i.hom_inv_id, Category.comp_id]
  let : Epi (G.map (factorThruImage f)) := by rw [he]; infer_instance
  let : StrongEpi (G.map (factorThruImage f)) := strongEpi_of_epi _
  let : Mono (G.map (image.ι f)) := by
    rw [← canonicalRegularImageIso_hom_ι T M f]
    infer_instance
  let : StrongEpi (H.map (factorThruImage f)) := by
    rw [recursive_map_conjugate η]
    infer_instance
  let : Mono (H.map (image.ι f)) := by
    rw [recursive_map_conjugate η]
    infer_instance
  refine ⟨image.isoStrongEpiMono (H.map (factorThruImage f)) (H.map (image.ι f))
    (by rw [← H.map_comp, image.fac]), ?_⟩
  exact image.isoStrongEpiMono_hom_comp_ι _ _ _

def recursiveRegularImageIso {X Y : TotalSplit T} (f : X ⟶ Y) :
    (recursiveDomainFunctor T M).obj (image f) ≅
      image ((recursiveDomainFunctor T M).map f) :=
  Classical.choose (preserves_recursive_regularImage T M f)

@[simp, reassoc] theorem recursiveRegularImageIso_hom_ι {X Y : TotalSplit T} (f : X ⟶ Y) :
    (recursiveRegularImageIso T M f).hom ≫ image.ι ((recursiveDomainFunctor T M).map f) =
      (recursiveDomainFunctor T M).map (image.ι f) :=
  Classical.choose_spec (preserves_recursive_regularImage T M f)

/-- Proposition 6.4 for the original recursive-carrier model interpretation
with its literal chosen idempotent domains, without a preservation assumption. -/
theorem recursive_regular : PreservesFiniteLimits (recursiveDomainFunctor T M) ∧
    PreservesFiniteCoproducts (recursiveDomainFunctor T M) ∧
    ∀ (X Y : TotalSplit T) (f : X ⟶ Y),
      ∃ e : (recursiveDomainFunctor T M).obj (image f) ≅
          image ((recursiveDomainFunctor T M).map f),
        e.hom ≫ image.ι ((recursiveDomainFunctor T M).map f) =
          (recursiveDomainFunctor T M).map (image.ι f) :=
  ⟨inferInstance, inferInstance,
    fun _ _ f => ⟨recursiveRegularImageIso T M f, recursiveRegularImageIso_hom_ι T M f⟩⟩

end CategoricalEssentialIncompleteness.V46.PredicateInterpretation
