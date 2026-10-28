/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.GlobalDomains
import CategoricalEssentialIncompleteness.EnrichedQuotients
import Mathlib.CategoryTheory.Types.Basic

/-!
# The global predicate functor and subobjects along `J`

The global predicate lattice is reindexed onto the genuine total-arrow category.
A natural family of order isomorphisms with the subobject lattices along `J`
induces a natural isomorphism of the underlying presheaves. The induced map
from ordinary restriction domains to subobjects is a natural injective bounded
lattice homomorphism.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe v u w v' u'
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness

namespace PredicateLattice
variable {A : Type u} [Category.{v} A] (P : PredicateLattice.{v, u, w} A)

/-- Reindex an indexed predicate lattice along an ordinary functor. -/
def comap {B : Type u'} [Category.{v'} B] (F : B ⥤ A) : PredicateLattice B where
  obj X := P.obj (F.obj X)
  lattice X := P.lattice (F.obj X)
  bounds X := P.bounds (F.obj X)
  pull f := P.pull (F.map f)
  pull_id X a := by rw [F.map_id, P.pull_id]
  pull_comp f g a := by rw [F.map_comp, P.pull_comp]

/-- The underlying contravariant predicate functor. -/
def presheaf : Aᵒᵖ ⥤ Type w where
  obj X := P.obj X.unop
  map f := ↾(P.pull f.unop)
  map_id X := by ext a; exact P.pull_id X.unop a
  map_comp f g := by ext a; exact P.pull_comp g.unop f.unop a

end PredicateLattice

/-- A natural identification with genuine subobjects along `J`, including their order. -/
structure SubobjectIdentification {A : Type u} [Category.{v} A]
    (P : PredicateLattice.{v, u, w} A) {C : Type u'} [Category.{v'} C] [HasPullbacks C]
    (J : A ⥤ C) where
  app : ∀ X, P.obj X ≃o Subobject (J.obj X)
  naturality : ∀ {X Y} (f : X ⟶ Y) (p : P.obj Y),
    app X (P.pull f p) = (Subobject.pullback (J.map f)).obj (app Y p)

namespace SubobjectIdentification
variable {A : Type u} [Category.{v} A] {P : PredicateLattice.{v, u, w} A}
variable {C : Type u'} [Category.{v'} C] [HasPullbacks C] {J : A ⥤ C}
variable (η : SubobjectIdentification P J)

/-- The componentwise identification gives a genuine natural isomorphism of presheaves.
Universe lifts only place the two presheaves in a common category of types. -/
def presheafIso :
    P.presheaf ⋙ uliftFunctor.{max u' v', w} ≅
      J.op ⋙ Subobject.functor C ⋙ uliftFunctor.{w, max u' v'} :=
  NatIso.ofComponents
    (fun X ↦
      { hom := ↾fun a ↦ ULift.up (η.app X.unop a.down)
        inv := ↾fun b ↦ ULift.up ((η.app X.unop).symm b.down)
        hom_inv_id := by
          ext a
          exact congrArg ULift.up ((η.app X.unop).symm_apply_apply a.down)
        inv_hom_id := by
          ext b
          exact congrArg ULift.up ((η.app X.unop).apply_symm_apply b.down) })
    (by
      intro X Y f
      ext p
      exact congrArg ULift.up (η.naturality f.unop p.down))

end SubobjectIdentification

namespace EnrichedRestriction
variable {V : Type u} [Category.{v} V] [HasFiniteLimits V] {O : Type w}
variable {H : InternalHom V O} (R : EnrichedRestriction H) (products : R.Products)
variable (P : InternalPredicates (R.totalHom products))

/-- Global predicates indexed by the ordinary category `Tot(K₀)`. -/
def predicatesOnTotals : PredicateLattice R.GlobalTotal :=
  P.globalPredicates.comap (R.fromGlobalTotal products)

variable [R.Zeros] [R.DomainLattices]
variable (j : InternalPredicateEmbedding (R.domainPredicates products) P)
variable {C : Type u'} [Category.{v'} C] [Regular C] [FinitaryExtensive C]
variable {J : R.GlobalTotal ⥤ C}
variable (η : SubobjectIdentification (R.predicatesOnTotals products P) J)

/-- Restriction domains mapped to subobjects through the internal embedding and `J`. -/
def domainSubobject (X : O) :
    BoundedLatticeHom (R.GlobalDomain X) (Subobject (J.obj (R.totalGlobalObject X))) where
  toFun a := η.app (R.totalGlobalObject X)
    ((j.app X).postcomp _ ((R.globalDomainOrderIso X).symm a))
  map_sup' := by intros; simp only [map_sup]
  map_inf' := by intros; simp only [map_inf]
  map_top' := by simp only [map_top]
  map_bot' := by simp only [map_bot]

@[simp] theorem domainSubobject_apply {X : O} (a : R.GlobalDomain X) :
    R.domainSubobject products P j η X a =
      η.app (R.totalGlobalObject X)
        ((R.globalDomainOrderIso X).symm a ≫ (j.app X).hom) := by
  change η.app (R.totalGlobalObject X)
    ((j.app X).postcomp _ ((R.globalDomainOrderIso X).symm a)) = _
  rw [InternalLatticeHom.postcomp_apply]

theorem domainSubobject_injective (X : O) :
    Function.Injective (R.domainSubobject products P j η X) := by
  intro a b h
  apply (R.globalDomainOrderIso X).symm.injective
  apply j.injective (⊤_ V) X
  exact (η.app (R.totalGlobalObject X)).injective h

/-- The domain-to-subobject comparison commutes with actual inverse image on both sides. -/
theorem domainSubobject_naturality {X Y : O}
    (f : R.totalGlobalObject X ⟶ R.totalGlobalObject Y) (a : R.GlobalDomain Y) :
    R.domainSubobject products P j η X (R.globalDomainInverse f.hom a) =
      (Subobject.pullback (J.map f)).obj (R.domainSubobject products P j η Y a) := by
  rw [R.domainSubobject_apply, R.domainSubobject_apply, ← η.naturality]
  apply congrArg (η.app (R.totalGlobalObject X))
  change (R.globalDomainOrderIso X).symm (R.globalDomainInverse f.hom a) ≫ (j.app X).hom =
    P.pull (R.globalTotalPoint f) ((R.globalDomainOrderIso Y).symm a ≫ (j.app Y).hom)
  refine Eq.trans ?_ (j.naturality (R.globalTotalPoint f)
    ((R.globalDomainOrderIso Y).symm a)).symm
  change (R.globalDomainEquiv X).symm (R.globalDomainInverse f.hom a) ≫ (j.app X).hom =
    R.domainInverse (R.globalTotalPoint f ≫ R.totalι X Y)
      ((R.globalDomainEquiv Y).symm a) ≫ (j.app X).hom
  apply congrArg (fun e : ⊤_ V ⟶ R.domainObject X ↦ e ≫ (j.app X).hom)
  exact (R.globalDomainInverse_point f.hom a).trans
    (congrArg (fun k : ⊤_ V ⟶ H.hom X Y ↦
      R.domainInverse k ((R.globalDomainEquiv Y).symm a)) (R.globalTotalPoint_ι f)).symm

end EnrichedRestriction
end CategoricalEssentialIncompleteness
