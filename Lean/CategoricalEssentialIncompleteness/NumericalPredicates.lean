/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.NumericalDomainEmbedding
import CategoricalEssentialIncompleteness.SubobjectPredicates
import CategoricalEssentialIncompleteness.GlobalSubobjects

/-!
# Numerical restriction domains and subobject predicates

Restriction domains and all PER subobjects give two contravariant families of
bounded distributive lattices on the category of total numerical arrows.
The support inclusion of a domain defines an injective natural bounded lattice
homomorphism between these families.
-/

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness
namespace Numerical

/-- Restriction domains, reindexed along total numerical arrows. -/
def domainPredicates : PredicateLattice Total where
  obj X := Domain X.obj
  lattice _ := inferInstance
  bounds _ := inferInstance
  pull f := domainInverseHom f
  pull_id X e := domainInverse_id X.obj e
  pull_comp f g e := domainInverse_comp f.hom g.hom e

/-- All subobjects in the PER category, restricted along the numerical functor. -/
def predicates : PredicateLattice Total :=
  (subobjectPredicates NumericalPER).comap toPER

/-- The numerical domain inclusion preserves bounds and lattice operations naturally. -/
def domainEmbedding : PredicateEmbedding domainPredicates predicates where
  app X := domainSubobjectHom X.obj
  injective X := domainSubobjectHom_injective X.obj
  naturality f e := domainSubobject_naturality f e

/-- Numerical predicates are the full subobject lattices along `toPER`. -/
def predicateSubobjectIdentification : SubobjectIdentification predicates toPER where
  app _ := OrderIso.refl _
  naturality _ _ := rfl

end Numerical
end CategoricalEssentialIncompleteness
