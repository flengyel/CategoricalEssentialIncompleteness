/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntaxSubstitutionTransportInputs

/-!
Parameter-dependent constructor squares are lifted to the constant-family morphisms,
using both product projections.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.SyntaxOperationsTransport
open SyntacticLists.Transport
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
variable (E : C ≌ D) {P : C} {Q : D} (b : E.functor.obj P ≅ Q)

omit [FinitaryExtensive C] [FinitaryExtensive D] in
theorem substitutionFamilyComparison_left {X : C} {X' : D} (i : E.functor.obj X ≅ X') :
    (coefficientComparison E b X X' i).hom.left = (SyntaxOptionTransport.productIso E b i).hom := by
  apply prod.hom_ext
  · exact (Over.w (coefficientComparison E b X X' i).hom).trans
      (SyntaxOptionTransport.productIso_fst E b i).symm
  · exact (coefficientComparison_snd E b X X' i).trans
      (SyntaxOptionTransport.productIso_snd E b i).symm

omit [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D] in
private theorem substitutionFamilyMap_left {A B : Over P} (f : A ⟶ B) :
    ((sliceEquivalence E b).functor.map f).left = E.functor.map f.left := rfl

omit [FinitaryExtensive C] [FinitaryExtensive D] in
/-- A square for an ordinary parameter-dependent root operation gives
the corresponding square in the parameter slice. -/
theorem map_substitution_parameterHom {X Y : C} {X' Y' : D}
    (i : E.functor.obj X ≅ X') (j : E.functor.obj Y ≅ Y')
    (h : P ⨯ X ⟶ Y) (h' : Q ⨯ X' ⟶ Y')
    (hh : E.functor.map h ≫ j.hom = (SyntaxOptionTransport.productIso E b i).hom ≫ h') :
    (sliceEquivalence E b).functor.map (parameterHom h) ≫
        (coefficientComparison E b Y Y' j).hom =
      (coefficientComparison E b X X' i).hom ≫ parameterHom h' := by
  apply Over.OverMorphism.ext
  apply prod.hom_ext
  · exact (Over.w ((sliceEquivalence E b).functor.map (parameterHom h) ≫
      (coefficientComparison E b Y Y' j).hom)).trans
        (Over.w ((coefficientComparison E b X X' i).hom ≫ parameterHom h')).symm
  · simp only [Over.comp_left,substitutionFamilyMap_left,Category.assoc]
    rw [coefficientComparison_snd,← Category.assoc,← E.functor.map_comp,
      parameterHom_value,parameterHom_value,substitutionFamilyComparison_left,hh]

def substitutionFamilyPairIso (A : C × C) (B : D × D)
    (i : (E.prod E).functor.obj A ≅ B) :
    ((sliceEquivalence E b).prod (sliceEquivalence E b)).functor.obj
        (constantFamily P A.1,constantFamily P A.2) ≅
      (constantFamily Q B.1,constantFamily Q B.2) :=
  SyntacticSyntax.Transport.carrierComparison E b A ≪≫
    ((constantFamilyFunctor Q).prod (constantFamilyFunctor Q)).mapIso i

def substitutionParameterInputIso (A : C × C) (B : D × D)
    (i : (E.prod E).functor.obj A ≅ B) (p : SyntaxPolynomial D) :
    (sliceEquivalence E b).functor.obj
        (((p.mapCoefficients E.inverse.obj).withParameters P).eval.obj
          (constantFamily P A.1,constantFamily P A.2)) ≅
      ((p.mapCoefficients id).withParameters Q).eval.obj
        (constantFamily Q B.1,constantFamily Q B.2) :=
  SyntacticSyntax.Transport.sliceComponent E b E.inverse.obj id (fun X => E.counitIso.app X) p
      (constantFamily P A.1,constantFamily P A.2) ≪≫
    ((p.mapCoefficients id).withParameters Q).eval.mapIso
      (substitutionFamilyPairIso E b A B i)

@[reassoc] theorem substitutionParameterInputIso_inl (A : C × C) (B : D × D)
    (i : (E.prod E).functor.obj A ≅ B) (p q : SyntaxPolynomial D) :
    (sliceEquivalence E b).functor.map
      (coprod.inl : ((p.mapCoefficients E.inverse.obj).withParameters P).eval.obj
        (constantFamily P A.1,constantFamily P A.2) ⟶
        (((SyntaxPolynomial.sum p q).mapCoefficients E.inverse.obj).withParameters P).eval.obj
          (constantFamily P A.1,constantFamily P A.2)) ≫
      (substitutionParameterInputIso E b A B i (.sum p q)).hom =
        (substitutionParameterInputIso E b A B i p).hom ≫ coprod.inl := by
  change (sliceEquivalence E b).functor.map coprod.inl ≫
    ((inv (coprodComparison (sliceEquivalence E b).functor _ _) ≫ coprod.map _ _) ≫
      coprod.map _ _) = _
  rw [← Category.assoc,← Category.assoc,map_inl_inv_coprodComparison,
    coprod.inl_map,Category.assoc,coprod.inl_map,← Category.assoc]
  rfl

@[reassoc] theorem substitutionParameterInputIso_inr (A : C × C) (B : D × D)
    (i : (E.prod E).functor.obj A ≅ B) (p q : SyntaxPolynomial D) :
    (sliceEquivalence E b).functor.map
      (coprod.inr : ((q.mapCoefficients E.inverse.obj).withParameters P).eval.obj
        (constantFamily P A.1,constantFamily P A.2) ⟶
        (((SyntaxPolynomial.sum p q).mapCoefficients E.inverse.obj).withParameters P).eval.obj
          (constantFamily P A.1,constantFamily P A.2)) ≫
      (substitutionParameterInputIso E b A B i (.sum p q)).hom =
        (substitutionParameterInputIso E b A B i q).hom ≫ coprod.inr := by
  change (sliceEquivalence E b).functor.map coprod.inr ≫
    ((inv (coprodComparison (sliceEquivalence E b).functor _ _) ≫ coprod.map _ _) ≫
      coprod.map _ _) = _
  rw [← Category.assoc,← Category.assoc,map_inr_inv_coprodComparison,
    coprod.inr_map,Category.assoc,coprod.inr_map,← Category.assoc]
  rfl

theorem substitutionParameterCopair_square (A : C × C) (B : D × D)
    (i : (E.prod E).functor.obj A ≅ B) (p q : SyntaxPolynomial D)
    {Z : C} {Z' : D} (j : E.functor.obj Z ≅ Z')
    (f : ((p.mapCoefficients E.inverse.obj).withParameters P).eval.obj
      (constantFamily P A.1,constantFamily P A.2) ⟶ constantFamily P Z)
    (g : ((q.mapCoefficients E.inverse.obj).withParameters P).eval.obj
      (constantFamily P A.1,constantFamily P A.2) ⟶ constantFamily P Z)
    (f' : ((p.mapCoefficients id).withParameters Q).eval.obj
      (constantFamily Q B.1,constantFamily Q B.2) ⟶ constantFamily Q Z')
    (g' : ((q.mapCoefficients id).withParameters Q).eval.obj
      (constantFamily Q B.1,constantFamily Q B.2) ⟶ constantFamily Q Z')
    (hf : (sliceEquivalence E b).functor.map f ≫ (coefficientComparison E b Z Z' j).hom =
      (substitutionParameterInputIso E b A B i p).hom ≫ f')
    (hg : (sliceEquivalence E b).functor.map g ≫ (coefficientComparison E b Z Z' j).hom =
      (substitutionParameterInputIso E b A B i q).hom ≫ g') :
    (sliceEquivalence E b).functor.map (coprod.desc f g) ≫
        (coefficientComparison E b Z Z' j).hom =
      (substitutionParameterInputIso E b A B i (.sum p q)).hom ≫ coprod.desc f' g' := by
  apply BinaryCofan.IsColimit.hom_ext
    (isColimitOfHasBinaryCoproductOfPreservesColimit (sliceEquivalence E b).functor _ _)
  · simp only [BinaryCofan.mk_inl]
    erw [← Category.assoc,← Functor.map_comp,coprod.inl_desc,hf,
      ← Category.assoc,substitutionParameterInputIso_inl]
    erw [Category.assoc (substitutionParameterInputIso E b A B i p).hom coprod.inl
      (coprod.desc f' g'),coprod.inl_desc]
  · simp only [BinaryCofan.mk_inr]
    erw [← Category.assoc,← Functor.map_comp,coprod.inr_desc,hg,
      ← Category.assoc,substitutionParameterInputIso_inr]
    erw [Category.assoc (substitutionParameterInputIso E b A B i q).hom coprod.inr
      (coprod.desc f' g'),coprod.inr_desc]

omit [FinitaryExtensive C] in
theorem substitution_constantFamily_map {X Y : C} (f : X ⟶ Y) :
    (constantFamilyFunctor P).map f = parameterHom ((prod.snd : P ⨯ X ⟶ X) ≫ f) := by
  apply Over.OverMorphism.ext
  apply prod.hom_ext <;> simp [parameterHom,constantFamilyFunctor]

omit [FinitaryExtensive C] [FinitaryExtensive D] in
theorem substitution_parameterize_square {X Y : C} {X' Y' : D}
    (i : E.functor.obj X ≅ X') (j : E.functor.obj Y ≅ Y')
    (f : X ⟶ Y) (f' : X' ⟶ Y')
    (hf : E.functor.map f ≫ j.hom = i.hom ≫ f') :
    E.functor.map ((prod.snd : P ⨯ X ⟶ X) ≫ f) ≫ j.hom =
      (SyntaxOptionTransport.productIso E b i).hom ≫ prod.snd ≫ f' := by
  rw [Functor.map_comp,Category.assoc,hf,← Category.assoc,
    ← SyntaxOptionTransport.productIso_snd,Category.assoc]

/-- Polynomial transport, the parameter comparison, and replacement of the recursive
carriers commute. Both parameter coordinates remain in the comparison throughout the
square. -/
theorem substitutionParameterInput_comparison (A : C × C) (B : D × D)
    (i : (E.prod E).functor.obj A ≅ B) (p : SyntaxPolynomial D) :
    (substitutionParameterInputIso E b A B i p).hom ≫
        SyntaxPolynomial.parameterComparison Q B (p.mapCoefficients id) =
      (sliceEquivalence E b).functor.map
          (SyntaxPolynomial.parameterComparison P A (p.mapCoefficients E.inverse.obj)) ≫
        (coefficientComparison E b ((p.mapCoefficients E.inverse.obj).eval.obj A)
          ((p.mapCoefficients id).eval.obj B) (substitutionPolynomialIso E A B i p)).hom := by
  let H := sliceEquivalence E b
  let q := p.mapCoefficients id
  let k := ((constantFamilyFunctor Q).prod (constantFamilyFunctor Q)).map i.hom
  have hn := SyntaxPolynomial.parameterComparison_natural Q i.hom q
  change (q.withParameters Q).eval.map k ≫ SyntaxPolynomial.parameterComparison Q B q =
    SyntaxPolynomial.parameterComparison Q ((E.prod E).functor.obj A) q ≫
      (constantFamilyFunctor Q).map (q.eval.map i.hom) at hn
  change ((SyntacticSyntax.Transport.sliceComponent E b E.inverse.obj id _ p
      (constantFamily P A.1,constantFamily P A.2)).hom ≫
    (q.withParameters Q).eval.map
      ((SyntacticSyntax.Transport.carrierComparison E b A).hom ≫ k)) ≫ _ = _
  rw [(q.withParameters Q).eval.map_comp,Category.assoc,Category.assoc,hn,
    ← Category.assoc,← Category.assoc]
  change ((SyntacticSyntax.Transport.parameterComponent E b E.inverse.obj id
      (fun X => E.counitIso.app X) p A).hom ≫
      SyntaxPolynomial.parameterComparison Q ((E.prod E).functor.obj A) q) ≫
      (constantFamilyFunctor Q).map (q.eval.map i.hom) = _
  rw [SyntacticSyntax.Transport.parameterComponent_comparison]
  simp only [coefficientComparison,substitutionPolynomialIso,Iso.trans_hom,Functor.mapIso_hom,
    Category.assoc,Functor.map_comp]
  rfl

/-- This lifts a proved parameter-dependent root square all the way from its slice
polynomial input to its output family. -/
theorem map_substitution_parameterOperation (A : C × C) (B : D × D)
    (i : (E.prod E).functor.obj A ≅ B) (p : SyntaxPolynomial D)
    {Z : C} {Z' : D} (j : E.functor.obj Z ≅ Z')
    (h : P ⨯ (p.mapCoefficients E.inverse.obj).eval.obj A ⟶ Z)
    (h' : Q ⨯ (p.mapCoefficients id).eval.obj B ⟶ Z')
    (hh : E.functor.map h ≫ j.hom =
      (SyntaxOptionTransport.productIso E b (substitutionPolynomialIso E A B i p)).hom ≫ h') :
    (sliceEquivalence E b).functor.map
        (SyntaxPolynomial.parameterComparison P A (p.mapCoefficients E.inverse.obj) ≫
          parameterHom h) ≫ (coefficientComparison E b Z Z' j).hom =
      (substitutionParameterInputIso E b A B i p).hom ≫
        SyntaxPolynomial.parameterComparison Q B (p.mapCoefficients id) ≫ parameterHom h' := by
  rw [Functor.map_comp,Category.assoc,map_substitution_parameterHom E b _ j h h' hh,
    ← Category.assoc,← substitutionParameterInput_comparison E b A B i p,Category.assoc]

end CategoricalEssentialIncompleteness.V46.SyntaxOperationsTransport
