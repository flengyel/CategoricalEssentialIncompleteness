/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46ArithmeticIndexedProvability

/-! # The uniform formula and the actual total family conclusion -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w t
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.ArithmeticIndexedProvability

private theorem inverse_arrow_map {D : Type u} {C : Type v}
    [Category.{w} D] [Category.{t} C] (E : D ≌ C)
    {P : C} {X : D} (f : P ⟶ E.functor.obj X) :
    E.functor.map (E.inverse.map f ≫ E.unitIso.inv.app X) =
      E.counitIso.hom.app P ≫ f := by
  rw [E.functor.map_comp,← E.counit_app_functor X]
  exact E.counit_naturality f

private theorem natural_apply {D : Type u} [Category.{w} D]
    (F G : D ⥤ Type) (η : F ≅ G) {X Y : D} (f : X ⟶ Y) (x : F.obj X) :
    (η.app Y).toEquiv (F.map f x) = G.map f ((η.app X).toEquiv x) :=
  ConcreteCategory.congr_hom (η.hom.naturality f) x

private theorem raw_chart_natural {D : Type u} {C : Type v}
    [Category.{w} D] [Category.{t} C] (E : D ≌ C)
    (F : D ⥤ Type) (H : C ⥤ Type) (η : F ≅ E.functor ⋙ H)
    {P : C} {X : D} (f : P ⟶ E.functor.obj X)
    (p : F.obj (E.inverse.obj P)) :
    (η.app X).toEquiv (F.map (E.inverse.map f ≫ E.unitIso.inv.app X) p) =
      H.map f (H.map (E.counitIso.hom.app P)
        ((η.app (E.inverse.obj P)).toEquiv p)) := by
  have h := natural_apply F (E.functor ⋙ H) η
    (E.inverse.map f ≫ E.unitIso.inv.app X) p
  exact h.trans (by
    change H.map (E.functor.map (E.inverse.map f ≫ E.unitIso.inv.app X))
      ((η.app (E.inverse.obj P)).toEquiv p) = _
    rw [inverse_arrow_map E f,Functor.map_comp_apply]
    rfl)

private theorem cancel_iso {C : Type u} [Category.{w} C] (H : C ⥤ Type)
    {X Y Z : C} (i : Y ≅ Z) (f : X ⟶ Z) (p : H.obj X) :
    H.map i.hom (H.map (f ≫ i.inv) p) = H.map f p := by
  have he : (f ≫ i.inv) ≫ i.hom = f := by
    rw [Category.assoc,Iso.inv_hom_id,Category.comp_id]
  exact (congrArg (fun k => k p) (H.map_comp (f ≫ i.inv) i.hom)).symm.trans
    (congrArg (fun k => H.map k p) he)

/-- Pointwise image stability is proved for an opaque categorical
pullback before applying the encoded numeral-fiber diagram. -/
theorem range_pullback_point {C : Type u} [Category.{w} C]
    (H : C ⥤ Type) {P Q S T : C}
    (i : Q ⟶ P) (c : Q ⟶ S) (d : P ⟶ T) (k : S ⟶ T)
    [PreservesLimit (cospan d k) H] (h : IsPullback i c d k) (s : H.obj S) :
    (∃ p : H.obj P, H.map d p = H.map k s) ↔
      ∃ q : H.obj Q, H.map c q = s := by
  constructor
  · rintro ⟨p,hp⟩
    obtain ⟨q,_,hq⟩ := Types.exists_of_isPullback (h.map H) p s hp
    exact ⟨q,hq⟩
  · rintro ⟨q,hq⟩
    refine ⟨H.map i q,?_⟩
    have he := congrArg (fun f => H.map f q) h.w
    rw [Functor.map_comp_apply,Functor.map_comp_apply] at he
    exact he.trans (congrArg (H.map k) hq)

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FailureOfComposition.ProofSearch FailureOfComposition.CodedObjectMembership
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open NamedArithmeticSignature

variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local notation "H" => PredicateInterpretation.totalFunctor 𝗣𝗔 M
local notation "E" => realization 𝗣𝗔
local notation "F" => SyntacticLists.F 𝗣𝗔 M

def proofChart (AxPA : Carrier) :
    Obj 𝗣𝗔 M (proofCarrier AxPA) ≃ (H).obj (ArithmeticIndexedFamily.sentenceProof AxPA) :=
  (((PredicateInterpretation.predicateComparison 𝗣𝗔 M).symm.app
      (proofCarrier AxPA)).toEquiv).trans
    ((H).mapIso ((predicateEquivalence 𝗣𝗔).counitIso.app
      (ArithmeticIndexedFamily.sentenceProof AxPA))).toEquiv

def productChart : Obj 𝗣𝗔 M ArithmeticIndexedAxioms.productPredicate ≃
    (H).obj (ArithmeticIndexedFamily.parameter ⨯ ArithmeticIndexedFamily.sentence) :=
  (((PredicateInterpretation.predicateComparison 𝗣𝗔 M).symm.app
      ArithmeticIndexedAxioms.productPredicate).toEquiv).trans
    ((H).mapIso ArithmeticIndexedAxioms.productIso).toEquiv

def rawPairPoint (e z : M)
    (hs : NamedArithmeticLiteralTotal.literalPredicate.val.Evalb ![z]) :
    Obj 𝗣𝗔 M ArithmeticIndexedAxioms.productPredicate :=
  ⟨⟪e,z⟫,(productCarrier_eval variableSymbols
    NamedArithmeticLiteralTotal.literalPredicate ⟪e,z⟫).mpr
      ⟨e,z,rfl,NamedArithmeticSignature.variables_eval e,hs⟩⟩

def productPoint (e z : M)
    (hs : NamedArithmeticLiteralTotal.literalPredicate.val.Evalb ![z]) :
    (H).obj (ArithmeticIndexedFamily.parameter ⨯ ArithmeticIndexedFamily.sentence) :=
  productChart M (rawPairPoint M e z hs)

theorem conclusion_chart (AxPA : Carrier) (p : Obj 𝗣𝗔 M (proofCarrier AxPA)) :
    (H).map (ArithmeticIndexedFamily.sentenceConclusion AxPA) (proofChart M AxPA p) =
      productChart M ((F).map (rawConclusion AxPA) p) := by
  have he := raw_chart_natural (predicateEquivalence 𝗣𝗔) (F) (H)
    (PredicateInterpretation.predicateComparison 𝗣𝗔 M).symm
    (ArithmeticIndexedFamily.sentenceConclusion AxPA ≫ ArithmeticIndexedAxioms.productIso.inv) p
  have hc := congrArg ((H).map ArithmeticIndexedAxioms.productIso.hom) he
  exact ((cancel_iso (H) ArithmeticIndexedAxioms.productIso
    (ArithmeticIndexedFamily.sentenceConclusion AxPA) (proofChart M AxPA p)).symm.trans hc.symm)

theorem provability_sentence (AxPA : Carrier) (e z : M)
    (h : (provability AxPA).val.Evalb ![e,z]) :
    NamedArithmeticLiteralTotal.literalPredicate.val.Evalb ![z] := by
  obtain ⟨p,hp⟩ := (provability_eval M AxPA e z).mp h
  have hy := ((F).map (rawConclusion AxPA) p).property
  have hd : ArithmeticIndexedAxioms.productPredicate.val.Evalb ![⟪e,z⟫] := hp ▸ hy
  obtain ⟨a,b,he,_,hb⟩ := (productCarrier_eval variableSymbols
    NamedArithmeticLiteralTotal.literalPredicate ⟪e,z⟫).mp hd
  obtain ⟨rfl,rfl⟩ := (pair_eq_pair_iff e z a b).mp he
  exact hb

/-- The formula represents the actual family conclusion image at the
parameter and literal sentence coordinates, at every internal input. -/
theorem provability_model (AxPA : Carrier) (e z : M)
    (hs : NamedArithmeticLiteralTotal.literalPredicate.val.Evalb ![z]) :
    (provability AxPA).val.Evalb ![e,z] ↔
      ∃ p : (H).obj (ArithmeticIndexedFamily.sentenceProof AxPA),
        (H).map (ArithmeticIndexedFamily.sentenceConclusion AxPA) p = productPoint M e z hs := by
  rw [provability_eval M AxPA e z]
  constructor
  · rintro ⟨p,hp⟩
    exact ⟨proofChart M AxPA p,(conclusion_chart M AxPA p).trans
      (congrArg (productChart M) (Subtype.ext hp))⟩
  · rintro ⟨p,hp⟩
    let q := (proofChart M AxPA).symm p
    have hq : proofChart M AxPA q = p := (proofChart M AxPA).apply_symm_apply p
    refine ⟨q,?_⟩
    have he : productChart M ((F).map (rawConclusion AxPA) q) =
        productChart M (rawPairPoint M e z hs) :=
      (conclusion_chart M AxPA q).symm.trans ((congrArg
        ((H).map (ArithmeticIndexedFamily.sentenceConclusion AxPA)) hq).trans hp)
    exact congrArg Subtype.val ((productChart M).injective he)

end CategoricalEssentialIncompleteness.V46.ArithmeticIndexedProvability
