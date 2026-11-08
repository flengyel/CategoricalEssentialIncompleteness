/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46MillerListsParameterInitial
import CategoricalEssentialIncompleteness.V46MillerSyntaxRawConstantComparison
import CategoricalEssentialIncompleteness.V46SyntacticListsTransport

/-! # Stable lists with the original nil and adjoin codes

The explicit parameter-list algebra is compared with the canonical
constant-family list algebra by a constructor-preserving isomorphism.
Initiality therefore includes every parameter object and every target
family. No condition on the ordinary computability of target values is
introduced.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.Miller.Lists
open Syntax.Raw
variable {P : Uniform.Family}

/-- The constructors on the canonical numerical list carrier. -/
def algebra (V : Total.Carrier P) : ListAlgebra (⟨V⟩ : Total.TotalCategory P) where
  carrier := object V
  nil := (baseComparison (object V) (object V) .unit).inv ≫ nil V
  cons := (baseComparison (object V) (object V) (consPolynomial V)).inv ≫ adjoinMap V

private theorem parameter_nil_lift (R : Total.TotalCategory P) (V : Total.Carrier P) :
    (liftIso R (object V) (object V) .unit).hom ≫ rawNil R V=
      explicitFamilyMap R (nil V) := by
  apply Over.OverMorphism.ext
  apply WideSubcategory.hom_ext
  apply Total.val_ext_on_source
  intro n hn
  let r := (Nat.unpair n).1
  have hn0 : (Nat.unpair n).2=0 := hn.2
  have hr : r ∈ R.obj.support := hn.1
  have he : n=Nat.pair r 0 := by simpa only [r,hn0] using (Nat.pair_unpair n).symm
  have hcode : constantLiftCode (.unit : SyntaxPolynomial (Total.TotalCategory P)) n=Nat.pair r 0 := by
    simp only [constantLiftCode,constantLift,hn0,r]
  have hc := (rawNil_graph R V r (Nat.pair r 0)).mpr ⟨hr,rfl⟩
  have hm : Nat.pair r 0 ∈ Total.val (explicitFamilyMap R (nil V)).left.hom n := by
    rw [he]
    exact (explicitFamilyMap_graph R (nil V) r 0 (Nat.pair r 0)).mpr
      ⟨hr,0,(nil_graph V 0 0).mpr ⟨rfl,rfl⟩,rfl⟩
  change Total.val ((liftIso R (object V) (object V) .unit).hom.left.hom ≫ (rawNil R V).left.hom) n=
    Total.val (explicitFamilyMap R (nil V)).left.hom n
  rw [Total.val_comp,liftIso_value R (object V) (object V) .unit n hn,Part.bind_some,hcode]
  exact (Part.eq_some_iff.mpr hc).trans (Part.eq_some_iff.mpr hm).symm

private theorem parameter_cons_lift (R : Total.TotalCategory P) (V : Total.Carrier P) :
    (liftIso R (object V) (object V) (consPolynomial V)).hom ≫ rawCons R V=
      explicitFamilyMap R (adjoinMap V) := by
  apply Over.OverMorphism.ext
  apply WideSubcategory.hom_ext
  apply Total.val_ext_on_source
  intro n hn
  let r := (Nat.unpair n).1
  let head := (Nat.unpair (Nat.unpair n).2).1
  let tail := (Nat.unpair (Nat.unpair n).2).2
  have he : n=Nat.pair r (Nat.pair head tail) := by
    simp only [r,head,tail,Nat.pair_unpair]
  have hh : head∈V.support := hn.2.1
  have ht : tail∈(carrier V).support := hn.2.2
  have hr : r ∈ R.obj.support := hn.1
  have hcode : constantLiftCode (consPolynomial V) n=Nat.pair r (Nat.pair head (Nat.pair r tail)) := by
    rw [he]
    simp only [constantLiftCode,constantLift,Nat.unpair_pair]
  have hc := (rawCons_graph R V r head tail (Nat.pair r (adjoin head tail))).mpr ⟨hr,hh,ht,rfl⟩
  have hm : Nat.pair r (adjoin head tail) ∈ Total.val (explicitFamilyMap R (adjoinMap V)).left.hom n := by
    rw [he]
    exact (explicitFamilyMap_graph R (adjoinMap V) r (Nat.pair head tail) _).mpr
      ⟨hr,adjoin head tail,(adjoin_graph V head tail _).mpr ⟨hh,ht,rfl⟩,rfl⟩
  change Total.val ((liftIso R (object V) (object V) (consPolynomial V)).hom.left.hom ≫ (rawCons R V).left.hom) n=
    Total.val (explicitFamilyMap R (adjoinMap V)).left.hom n
  rw [Total.val_comp,liftIso_value R (object V) (object V) (consPolynomial V) n hn,Part.bind_some,hcode]
  exact (Part.eq_some_iff.mpr hc).trans (Part.eq_some_iff.mpr hm).symm

private theorem withParameters_nil {D : Type*} [Category D] [HasFiniteLimits D]
    [HasFiniteCoproducts D] {V : D} (L : ListAlgebra V) (R : D) :
    constantUnitComparison R ≫ (constantFamilyFunctor R).map L.nil=(L.withParameters R).nil := by
  apply Over.OverMorphism.ext
  apply prod.hom_ext
  · simp [constantUnitComparison,constantFamilyFunctor,ListAlgebra.withParameters]
  · simp [constantUnitComparison,constantFamilyFunctor,ListAlgebra.withParameters]

private theorem withParameters_cons {D : Type*} [Category D] [HasFiniteLimits D]
    [HasFiniteCoproducts D] {V : D} (L : ListAlgebra V) (R : D) :
    constantProductComparison R V L.carrier ≫ (constantFamilyFunctor R).map L.cons=
      (L.withParameters R).cons := by
  apply Over.OverMorphism.ext
  apply prod.hom_ext
  · simp [constantProductComparison,constantFamilyFunctor,ListAlgebra.withParameters]
  · simp [constantProductComparison,constantFamilyFunctor,ListAlgebra.withParameters]

private theorem nil_polynomial_constructor (R : Total.TotalCategory P) (V : Total.Carrier P) :
    constantPolynomialLeft R (object V) (object V) .unit ≫
        (constantFamilyFunctor R).map (algebra V).nil=
      (liftIso R (object V) (object V) .unit).hom ≫ rawNil R V ≫
        (explicitFamilyIso R (object V)).hom := by
  rw [constantPolynomialSquare]
  unfold constantPolynomialRight
  rw [Category.assoc,← Functor.map_comp]
  simp only [algebra,Iso.hom_inv_id_assoc]
  rw [← explicitFamilyMap_natural,← parameter_nil_lift]
  simp only [Category.assoc]

private theorem cons_polynomial_constructor (R : Total.TotalCategory P) (V : Total.Carrier P) :
    constantPolynomialLeft R (object V) (object V) (consPolynomial V) ≫
        (constantFamilyFunctor R).map (algebra V).cons=
      (liftIso R (object V) (object V) (consPolynomial V)).hom ≫ rawCons R V ≫
        (explicitFamilyIso R (object V)).hom := by
  rw [constantPolynomialSquare]
  unfold constantPolynomialRight
  rw [Category.assoc,← Functor.map_comp]
  simp only [algebra,Iso.hom_inv_id_assoc]
  rw [← explicitFamilyMap_natural,← parameter_cons_lift]
  simp only [Category.assoc]

theorem parameterAlgebra_nil (R : Total.TotalCategory P) (V : Total.Carrier P) :
    (parameterAlgebra R V).nil ≫ (explicitFamilyIso R (object V)).hom=
      ((algebra V).withParameters R).nil := by
  apply (cancel_epi ((liftIso R (object V) (object V) .unit).hom ≫
    (comparison R (family R V) (family R V) .unit).hom)).mp
  have h := nil_polynomial_constructor R V
  rw [constantPolynomialLeft_direct] at h
  simp only [Category.assoc] at h
  change (liftIso R (object V) (object V) .unit).hom ≫
    (comparison R (constantObject R (object V)) (constantObject R (object V)) .unit).hom ≫
      (𝟙 (⊤_ (Over R))) ≫ constantUnitComparison R ≫ (constantFamilyFunctor R).map (algebra V).nil = _ at h
  erw [Category.id_comp,withParameters_nil] at h
  simp only [parameterAlgebra,Category.assoc,Iso.hom_inv_id_assoc]
  change (liftIso R (object V) (object V) .unit).hom ≫ rawNil R V ≫ (explicitFamilyIso R (object V)).hom =
    (liftIso R (object V) (object V) .unit).hom ≫
      (comparison R (constantObject R (object V)) (constantObject R (object V)) .unit).hom ≫
        ((algebra V).withParameters R).nil
  exact h.symm

theorem parameterAlgebra_cons (R : Total.TotalCategory P) (V : Total.Carrier P) :
    (parameterAlgebra R V).cons ≫ (explicitFamilyIso R (object V)).hom=
      prod.map (𝟙 (constantFamily R (⟨V⟩ : Total.TotalCategory P))) (explicitFamilyIso R (object V)).hom ≫
        ((algebra V).withParameters R).cons := by
  apply (cancel_epi ((liftIso R (object V) (object V) (consPolynomial V)).hom ≫
    (comparison R (family R V) (family R V) (consPolynomial V)).hom)).mp
  have h := cons_polynomial_constructor R V
  rw [constantPolynomialLeft_direct] at h
  simp only [Category.assoc] at h
  dsimp only [consPolynomial,SyntaxPolynomial.withParameters,SyntaxPolynomial.eval,
    SyntaxPolynomial.productFunctor,SyntaxPolynomial.parameterComparison] at h
  erw [prod.map_id_id,Category.id_comp] at h
  change (liftIso R (object V) (object V) (consPolynomial V)).hom ≫
    (comparison R (constantObject R (object V)) (constantObject R (object V)) (consPolynomial V)).hom ≫
      prod.map (𝟙 (constantFamily R (⟨V⟩ : Total.TotalCategory P))) (explicitFamilyIso R (object V)).hom ≫
        constantProductComparison R (⟨V⟩ : Total.TotalCategory P) (object V) ≫
          (constantFamilyFunctor R).map (algebra V).cons = _ at h
  have hc := withParameters_cons (algebra V) R
  change constantProductComparison R (⟨V⟩ : Total.TotalCategory P) (object V) ≫
    (constantFamilyFunctor R).map (algebra V).cons = ((algebra V).withParameters R).cons at hc
  have hh := (congrArg (fun k => (liftIso R (object V) (object V) (consPolynomial V)).hom ≫
    ((comparison R (constantObject R (object V)) (constantObject R (object V)) (consPolynomial V)).hom ≫
      (prod.map (𝟙 (constantFamily R (⟨V⟩ : Total.TotalCategory P))) (explicitFamilyIso R (object V)).hom ≫ k))) hc).symm.trans h
  simp only [parameterAlgebra,Category.assoc,Iso.hom_inv_id_assoc]
  change (liftIso R (object V) (object V) (consPolynomial V)).hom ≫ rawCons R V ≫ (explicitFamilyIso R (object V)).hom =
    (liftIso R (object V) (object V) (consPolynomial V)).hom ≫
      (comparison R (constantObject R (object V)) (constantObject R (object V)) (consPolynomial V)).hom ≫
        prod.map (𝟙 (constantFamily R (⟨V⟩ : Total.TotalCategory P))) (explicitFamilyIso R (object V)).hom ≫
          ((algebra V).withParameters R).cons
  exact hh.symm

/-- Full constructor comparison on the exact list carrier. -/
def parameterAlgebraIso (R : Total.TotalCategory P) (V : Total.Carrier P) :
    (parameterAlgebra R V).asAlgebra ≅ ((algebra V).withParameters R).asAlgebra :=
  SyntacticLists.Transport.constructorsIso _ _ (explicitFamilyIso R (object V))
    (parameterAlgebra_nil R V) (parameterAlgebra_cons R V)

def withParametersInitial (R : Total.TotalCategory P) (V : Total.Carrier P) :
    IsInitial ((algebra V).withParameters R).asAlgebra :=
  (parameterInitial R V).ofIso (parameterAlgebraIso R V)

def initial (V : Total.Carrier P) : IsInitial (algebra V).asAlgebra :=
  SyntacticLists.Transport.initialOfTerminalParameters (algebra V)
    (withParametersInitial (⊤_ (Total.TotalCategory P)) V)

/-- The original list algebra is initial in the base and every slice. -/
def stable (V : Total.Carrier P) : StableListAlgebra (⟨V⟩ : Total.TotalCategory P) where
  algebra := algebra V
  initial := initial V
  stable := fun R => withParametersInitial R V

end CategoricalEssentialIncompleteness.V46.Miller.Lists
