/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerNamedProofImageLogicalReflection

/-! # All seven-scheme parameters yield finite Hilbert proofs from Γ

The target success points prove both free-for conditions and their literal
substitution results. The distribution parameter is reflected through the false
classifier and the PA false fiber. No logical scheme coverage, source axiom
admissibility or semantic validity premise is supplied.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage
namespace SchemeReflection
open NamedFiniteSyntax NamedPostfixEncoding
open Points
variable (P : Uniform.Family) (σ π : ℕ → Carrier) (d : ℕ) (Γ : Set ℕ)
local notation "F" => Syntax.predicateFunctor P
local notation "U" => Total.underlying (P:=P)
local notation "N" => PredicateInterpretation.functor 𝗣𝗔 ℕ
local notation "V" => (variableCarrier : PredicateCategory 𝗣𝗔)
local notation "S₀" => NamedSyntaxComparison.sourceSyntax (V) σ π d
local notation "S" => syntaxData P σ π d
local notation "Fm" => NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d

private theorem decode_sourceFormula (q : PredicateInterpretation.Obj ℕ (S₀).algebra.a.2) :
    decodeFormula P σ π d ((U).map (NamedSyntaxComparison.formulaIso P (V) σ π d).inv
      (sourcePoint P _ q))=NamedPlainSemantics.decodeFormula σ π d q := by
  change (NamedPostfixPlainComparison.plainFormulaModelEquiv σ π d).symm
    ((sourcePointEquiv P (S₀).algebra.a.2).symm
      ((U).map (NamedSyntaxComparison.formulaIso P (V) σ π d).hom
        ((U).map (NamedSyntaxComparison.formulaIso P (V) σ π d).inv (sourcePoint P _ q))))=_
  rw [← CategoryTheory.Functor.map_comp_apply,Iso.inv_hom_id,CategoryTheory.Functor.map_id_apply]
  rfl

private theorem mapped_iso_injective {C : Type} [Category C] (G : C ⥤ Type)
    {A B : C} (i : A ≅ B) : Function.Injective (G.map i.hom) := by
  intro x y hxy
  have h := congrArg (G.map i.inv) hxy
  simpa only [← CategoryTheory.Functor.map_comp_apply,Iso.hom_inv_id,
    CategoryTheory.Functor.map_id_apply] using h

theorem source_point_reflection (A₀ B₀ : PredicateCategory 𝗣𝗔)
    (X₀ Y₀ : Total.TotalCategory P) (e : (F).obj A₀ ≅ X₀) (β : (F).obj B₀ ≅ Y₀)
    (f a : A₀ ⟶ B₀) (g c : X₀ ⟶ Y₀)
    (hs : e.hom ≫ g=(F).map f ≫ β.hom)
    (hc : e.hom ≫ c=(F).map a ≫ β.hom)
    (q₀ : (N).obj A₀) (x : (U).obj X₀)
    (hq : (U).map e.hom (sourcePoint P A₀ q₀)=x)
    (ht : (U).map g x=(U).map c x) : (N).map f q₀=(N).map a q₀ := by
  have hf := congrArg (fun k : (F).obj A₀ ⟶ Y₀ => (U).map k (sourcePoint P A₀ q₀)) hs
  have ha := congrArg (fun k : (F).obj A₀ ⟶ Y₀ => (U).map k (sourcePoint P A₀ q₀)) hc
  simp only [CategoryTheory.Functor.map_comp_apply,map_sourcePoint,hq] at hf ha
  have hinj : Function.Injective ((U).map β.hom) := mapped_iso_injective (U) β
  have hi : sourcePoint P B₀ ((N).map f q₀)=sourcePoint P B₀ ((N).map a q₀) :=
    @hinj (sourcePoint P B₀ ((N).map f q₀)) (sourcePoint P B₀ ((N).map a q₀))
      (hf.symm.trans (ht.trans ha))
  apply Subtype.ext
  simpa only [sourcePoint] using congrArg Subtype.val hi

private theorem charted_operation_value {A B : PredicateCategory 𝗣𝗔}
    {X Y : Total.TotalCategory P} (i : (F).obj A ≅ X) (j : (F).obj B ≅ Y)
    (a : A ⟶ B) (g : X ⟶ Y) (h : (F).map a ≫ j.hom=i.hom ≫ g)
    (q : PredicateInterpretation.Obj ℕ A) (x : (U).obj X)
    (hx : (U).map i.hom (sourcePoint P A q)=x) :
    (U).map g x=(U).map j.hom (sourcePoint P B ((N).map a q)) := by
  have hh := congrArg (fun f : (F).obj A ⟶ Y => (U).map f (sourcePoint P A q)) h
  simp only [CategoryTheory.Functor.map_comp_apply,map_sourcePoint,hx] at hh
  exact hh.symm

/-- Every target false-fiber point determines a source PA false-fiber
point; the construction uses the complete classifier comparison. -/
theorem distribution_absent (p : (U).obj (S).distributionParameters) :
    let base := (U).map (S).distributionInclusion p
    ((U).map prod.fst base).val ∉
      (decodeFormula P σ π d ((U).map prod.fst ((U).map prod.snd base))).freeVariables := by
  let base := (U).map (S).distributionInclusion p
  let J := distributionBaseChart P σ π d
  let i := NamedSyntaxComparison.formulaIso P (V) σ π d
  let K := NamedSyntaxComparison.Options.productIso (F) i.symm i.symm
  let B₀ : PredicateCategory 𝗣𝗔 := Limits.prod (C := PredicateCategory 𝗣𝗔) (V)
    (Limits.prod (C := PredicateCategory 𝗣𝗔) (S₀).algebra.a.2 (S₀).algebra.a.2)
  let B₁ : Total.TotalCategory P := (F).obj (V) ⨯ ((S).algebra.a.2 ⨯ (S).algebra.a.2)
  let name₀ := prod.fst (C := PredicateCategory 𝗣𝗔) (X := (V))
    (Y := Limits.prod (C := PredicateCategory 𝗣𝗔) (S₀).algebra.a.2 (S₀).algebra.a.2)
  let tail₀ := prod.snd (C := PredicateCategory 𝗣𝗔) (X := (V))
    (Y := Limits.prod (C := PredicateCategory 𝗣𝗔) (S₀).algebra.a.2 (S₀).algebra.a.2)
  let first₀ := prod.fst (C := PredicateCategory 𝗣𝗔) (X := (S₀).algebra.a.2) (Y := (S₀).algebra.a.2)
  let name₁ : B₁ ⟶ (F).obj (V) := prod.fst
  let tail₁ : B₁ ⟶ (S).algebra.a.2 ⨯ (S).algebra.a.2 := prod.snd
  let first₁ : (S).algebra.a.2 ⨯ (S).algebra.a.2 ⟶ (S).algebra.a.2 := prod.fst
  let q₀ := (sourcePointEquiv P B₀).symm ((U).map J.inv base)
  let point₀ := sourcePoint P B₀ q₀
  have hq : (U).map J.hom (sourcePoint P B₀ q₀)=base := by
    change (U).map J.hom ((sourcePointEquiv P B₀)
      ((sourcePointEquiv P B₀).symm ((U).map J.inv base)))=base
    rw [Equiv.apply_symm_apply,← CategoryTheory.Functor.map_comp_apply,Iso.inv_hom_id,
      CategoryTheory.Functor.map_id_apply]
  have ht : (U).map (S).distributionAbsence base=(U).map (Two.constant B₁ false) base := by
    have h := congrArg (fun f => (U).map f p) (S).distribution_absence
    have hc := congrArg (fun f => (U).map f p) (Two.comp_constant (S).distributionInclusion false)
    simp only [CategoryTheory.Functor.map_comp_apply] at h hc
    exact h.trans hc.symm
  have hconstant : J.hom ≫ Two.constant B₁ false=
      (F).map (Two.constant B₀ false) ≫ (Derivation.booleanIso (F)).hom :=
    (Two.comp_constant J.hom false).trans
      (NamedSyntaxComparison.ListTransport.map_constant (F) B₀ false).symm
  have hsource : (N).map (S₀).distributionAbsence q₀=(N).map (Two.constant B₀ false) q₀ :=
    source_point_reflection P B₀ (Two (PredicateCategory 𝗣𝗔)) B₁
      (Two (Total.TotalCategory P)) J (Derivation.booleanIso (F))
      (S₀).distributionAbsence (Two.constant B₀ false) (S).distributionAbsence
      (Two.constant B₁ false) (distributionAbsence_comparison P σ π d) hconstant q₀ base hq ht
  obtain ⟨r₀,hr₀⟩ := SyntacticNamedHilbert.booleanFiber_point_exists 𝗣𝗔 ℕ
    (S₀).distributionAbsence false q₀ hsource
  have ha := NamedPlainSemantics.distribution_absent σ π d r₀
  change ((N).map name₀ ((N).map (S₀).distributionInclusion r₀)).val ∉
    (NamedPlainSemantics.decodeFormula σ π d
      ((N).map first₀ ((N).map tail₀ ((N).map (S₀).distributionInclusion r₀)))).freeVariables at ha
  let sourceAbsent (v : (N).obj B₀) : Prop := ((N).map name₀ v).val ∉
    (NamedPlainSemantics.decodeFormula σ π d ((N).map first₀ ((N).map tail₀ v))).freeVariables
  have ha₀ : sourceAbsent q₀ := (congrArg sourceAbsent hr₀).mp ha
  have hname : J.hom ≫ name₁=(F).map name₀ := by
    have h := NamedSyntaxComparison.Options.productIso_fst (F) (Iso.refl ((F).obj (V))) K
    simpa only [J,K,distributionBaseChart,name₀,name₁,Iso.refl_hom,Category.comp_id] using h
  have hx : ((N).map name₀ q₀).val=((U).map name₁ base).val := by
    have hc := congrArg (fun f : (F).obj B₀ ⟶ (F).obj (V) => (U).map f point₀) hname
    have hpoint := (congrArg ((U).map name₁) hq.symm).trans
      ((CategoryTheory.Functor.map_comp_apply (U) J.hom name₁ point₀).symm.trans
        (hc.trans (map_sourcePoint P name₀ q₀)))
    exact (congrArg Subtype.val hpoint).symm
  have houter := NamedSyntaxComparison.Options.productIso_snd (F) (Iso.refl ((F).obj (V))) K
  have hinner := NamedSyntaxComparison.Options.productIso_fst (F) i.symm i.symm
  have h₀ := congrArg (fun f : (F).obj B₀ ⟶ (S).algebra.a.2 ⨯ (S).algebra.a.2 =>
    f ≫ first₁) houter
  have h₁ := congrArg (fun f : (F).obj ((S₀).algebra.a.2 ⨯ (S₀).algebra.a.2) ⟶ (S).algebra.a.2 =>
    (F).map tail₀ ≫ f) hinner
  have hpath : J.hom ≫ (tail₁ ≫ first₁)=(F).map tail₀ ≫ (F).map first₀ ≫ i.inv :=
    (Category.assoc _ _ _).symm.trans (h₀.trans ((Category.assoc _ _ _).trans h₁))
  have hsquare : (F).map (tail₀ ≫ first₀) ≫ i.inv=J.hom ≫ (tail₁ ≫ first₁) := by
    simpa only [CategoryTheory.Functor.map_comp,Category.assoc] using hpath.symm
  have hvalue := charted_operation_value P J i.symm (tail₀ ≫ first₀)
    (tail₁ ≫ first₁) hsquare q₀ base hq
  have hformula : decodeFormula P σ π d ((U).map first₁ ((U).map tail₁ base))=
      NamedPlainSemantics.decodeFormula σ π d ((N).map first₀ ((N).map tail₀ q₀)) := by
    have hv := congrArg (decodeFormula P σ π d) hvalue
    have hl := congrArg (decodeFormula P σ π d)
      ((U).map_comp_apply tail₁ first₁ base)
    have hr := decode_sourceFormula P σ π d ((N).map (tail₀ ≫ first₀) q₀)
    have hn := congrArg (NamedPlainSemantics.decodeFormula σ π d)
      ((N).map_comp_apply tail₀ first₀ q₀)
    exact hl.symm.trans (hv.trans (hr.trans hn))
  exact (congrArg₂ (fun n φ => n ∉ Formula.freeVariables φ) hx hformula.symm).mp ha₀

end SchemeReflection
end CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage
