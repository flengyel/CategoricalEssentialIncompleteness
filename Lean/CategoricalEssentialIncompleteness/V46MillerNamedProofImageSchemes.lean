/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46MillerNamedProofImageSchemePoints

/-! # Seven literal scheme witnesses in the actual uniform parameter objects -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage
namespace Points
open NamedFiniteSyntax NamedPostfixEncoding
variable (P : Uniform.Family) (σ π : ℕ → Carrier) (d : ℕ)
local notation "F" => Syntax.predicateFunctor P
local notation "U" => Total.underlying (P:=P)
local notation "N" => PredicateInterpretation.functor 𝗣𝗔 ℕ
local notation "V" => (variableCarrier : PredicateCategory 𝗣𝗔)
local notation "S₀" => NamedSyntaxComparison.sourceSyntax (V) σ π d
local notation "S" => syntaxData P σ π d
local notation "Tm" => NamedFiniteSyntax.Term (Symbols σ) d
local notation "Fm" => NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d

def distributionBaseChart : (F).obj ((V) ⨯ ((S₀).algebra.a.2 ⨯ (S₀).algebra.a.2)) ≅
    (F).obj (V) ⨯ ((S).algebra.a.2 ⨯ (S).algebra.a.2) :=
  NamedSyntaxComparison.Options.productIso (F) (Iso.refl _)
    (NamedSyntaxComparison.Options.productIso (F)
      (NamedSyntaxComparison.formulaIso P (V) σ π d).symm
      (NamedSyntaxComparison.formulaIso P (V) σ π d).symm)

theorem distributionAbsence_comparison :
    (distributionBaseChart P σ π d).hom ≫ (S).distributionAbsence=
      (F).map (S₀).distributionAbsence ≫ (Derivation.booleanIso (F)).hom := by
  let J := distributionBaseChart P σ π d
  let c₀ := prod.lift (C := PredicateCategory 𝗣𝗔)
    (prod.fst (C := PredicateCategory 𝗣𝗔) (X := (V))
      (Y := Limits.prod (C := PredicateCategory 𝗣𝗔) (S₀).algebra.a.2 (S₀).algebra.a.2))
    (prod.snd (C := PredicateCategory 𝗣𝗔) (X := (V))
      (Y := Limits.prod (C := PredicateCategory 𝗣𝗔) (S₀).algebra.a.2 (S₀).algebra.a.2) ≫
        prod.fst (C := PredicateCategory 𝗣𝗔) (X := (S₀).algebra.a.2) (Y := (S₀).algebra.a.2) ≫
          (S₀).formulaOccurrences)
  let c₁ := prod.lift
    (prod.fst : (F).obj (V) ⨯ ((S).algebra.a.2 ⨯ (S).algebra.a.2) ⟶ (F).obj (V))
    (prod.snd ≫ prod.fst ≫ (S).formulaOccurrences)
  have ho : (F).map (S₀).formulaOccurrences=
      (NamedSyntaxComparison.formulaIso P (V) σ π d).inv ≫ (S).formulaOccurrences := by
    let i := NamedSyntaxComparison.formulaIso P (V) σ π d
    have hh := congrArg (fun k : (S).algebra.a.2 ⟶ (S).lists.algebra.carrier => i.inv ≫ k)
      (NamedSyntaxComparison.formulaOccurrences_comparison P (V) σ π d)
    change i.inv ≫ (i.hom ≫ (F).map (S₀).formulaOccurrences)=
      i.inv ≫ (S).formulaOccurrences at hh
    have hc : (i.inv ≫ i.hom) ≫ (F).map (S₀).formulaOccurrences=
        (F).map (S₀).formulaOccurrences := by
      rw [Iso.inv_hom_id,Category.id_comp]
    exact hc.symm.trans ((Category.assoc _ _ _).trans hh)
  have hfst : J.hom ≫ prod.fst=(F).map
      (prod.fst (C := PredicateCategory 𝗣𝗔) (X := (V))
        (Y := Limits.prod (C := PredicateCategory 𝗣𝗔) (S₀).algebra.a.2 (S₀).algebra.a.2)) := by
    simpa only [J,distributionBaseChart,Iso.refl_hom,Category.comp_id] using
      NamedSyntaxComparison.Options.productIso_fst (F) (Iso.refl ((F).obj (V)))
        (NamedSyntaxComparison.Options.productIso (F)
          (NamedSyntaxComparison.formulaIso P (V) σ π d).symm
          (NamedSyntaxComparison.formulaIso P (V) σ π d).symm)
  have hsnd : J.hom ≫ (prod.snd ≫ prod.fst ≫ (S).formulaOccurrences)=
      (F).map (prod.snd ≫ prod.fst ≫ (S₀).formulaOccurrences) := by
    let i := NamedSyntaxComparison.formulaIso P (V) σ π d
    let k := NamedSyntaxComparison.Options.productIso (F) i.symm i.symm
    have h₀ := NamedSyntaxComparison.Options.productIso_snd (F) (Iso.refl ((F).obj (V))) k
    have h₁ := NamedSyntaxComparison.Options.productIso_fst (F) i.symm i.symm
    have hh₀ := congrArg (fun z => z ≫ prod.fst ≫ (S).formulaOccurrences) h₀
    have hh₁ := congrArg (fun z => (F).map
      (prod.snd (C := PredicateCategory 𝗣𝗔) (X := (V))
        (Y := Limits.prod (C := PredicateCategory 𝗣𝗔) (S₀).algebra.a.2 (S₀).algebra.a.2)) ≫
          z ≫ (S).formulaOccurrences) h₁
    have hh₂ := congrArg (fun z => (F).map
      (prod.snd (C := PredicateCategory 𝗣𝗔) (X := (V))
        (Y := Limits.prod (C := PredicateCategory 𝗣𝗔) (S₀).algebra.a.2 (S₀).algebra.a.2)) ≫
          (F).map (prod.fst (C := PredicateCategory 𝗣𝗔)
            (X := (S₀).algebra.a.2) (Y := (S₀).algebra.a.2)) ≫ z) ho.symm
    simp only [Category.assoc] at hh₀ hh₁
    have hh := hh₀.trans (hh₁.trans hh₂)
    simp only [CategoryTheory.Functor.map_comp]
    exact hh
  have hp : J.hom ≫ c₁=(F).map c₀ ≫ prodComparison (F) (V) (S₀).lists.algebra.carrier := by
    have hh := congrArg₂ (fun f g => prod.lift f g) hfst hsnd
    have hl := NamedSyntaxComparison.ListTransport.map_lift (F)
      (prod.fst (C := PredicateCategory 𝗣𝗔) (X := (V))
        (Y := Limits.prod (C := PredicateCategory 𝗣𝗔) (S₀).algebra.a.2 (S₀).algebra.a.2))
      (prod.snd (C := PredicateCategory 𝗣𝗔) (X := (V))
        (Y := Limits.prod (C := PredicateCategory 𝗣𝗔) (S₀).algebra.a.2 (S₀).algebra.a.2) ≫
          prod.fst (C := PredicateCategory 𝗣𝗔) (X := (S₀).algebra.a.2)
            (Y := (S₀).algebra.a.2) ≫ (S₀).formulaOccurrences)
    exact (prod.comp_lift _ _ _).trans (hh.trans hl.symm)
  have hm : (F).map ((S₀).lists.membership (S₀).decidableVariables) ≫
      (Derivation.booleanIso (F)).hom=
        prodComparison (F) (V) (S₀).lists.algebra.carrier ≫
          (S).lists.membership (S).decidableVariables := by
    convert NamedSyntaxComparison.ListTransport.map_membership P (V) (S₀).decidableVariables using 1
    all_goals rfl
  change J.hom ≫ (c₁ ≫ (S).lists.membership (S).decidableVariables)=
    (F).map (c₀ ≫ (S₀).lists.membership (S₀).decidableVariables) ≫ _
  have ht := congrArg (fun z => z ≫ (S).lists.membership (S).decidableVariables) hp
  have hg := congrArg (fun z => (F).map c₀ ≫ z) hm.symm
  have hb := congrArg (fun z => z ≫ (Derivation.booleanIso (F)).hom)
    ((F).map_comp c₀ ((S₀).lists.membership (S₀).decidableVariables)).symm
  exact (Category.assoc _ _ _).symm.trans (ht.trans
    ((Category.assoc _ _ _).trans (hg.trans ((Category.assoc _ _ _).symm.trans hb))))

private theorem distributionMap_condition :
    ((F).map (S₀).distributionInclusion ≫ (distributionBaseChart P σ π d).hom) ≫
      (S).distributionAbsence=
    ((F).map (S₀).distributionInclusion ≫ (distributionBaseChart P σ π d).hom) ≫
      Two.constant ((F).obj (V) ⨯ ((S).algebra.a.2 ⨯ (S).algebra.a.2)) false := by
  rw [Category.assoc,distributionAbsence_comparison,← Category.assoc,
    ← CategoryTheory.Functor.map_comp,CategoricalSyntax.distribution_absence,
    NamedSyntaxComparison.ListTransport.map_constant,Two.comp_constant]

def distributionMap : (F).obj (S₀).distributionParameters ⟶ (S).distributionParameters :=
  equalizer.lift ((F).map (S₀).distributionInclusion ≫ (distributionBaseChart P σ π d).hom)
    (distributionMap_condition P σ π d)

theorem distributionMap_inclusion :
    distributionMap P σ π d ≫ (S).distributionInclusion=
      (F).map (S₀).distributionInclusion ≫ (distributionBaseChart P σ π d).hom :=
  equalizer.lift_ι _ _

theorem distributionPoint_exists (x : ℕ) (φ ψ : Fm) (h : x ∉ φ.freeVariables) :
    ∃ z : (U).obj (S).distributionParameters,
      (U).map (S).distributionInclusion z=
        pairPoint (namePoint P x) (pairPoint (formulaPoint P σ π d φ) (formulaPoint P σ π d ψ)) := by
  obtain ⟨z₀,hz₀⟩ := SyntacticNamedHilbert.distributionPoint_exists σ π d x φ ψ h
  let point₀ := sourcePoint P (S₀).distributionParameters z₀
  have h₀ := (Functor.map_comp_apply (U) (distributionMap P σ π d)
    (S).distributionInclusion point₀).symm
  have h₁ := congrArg (fun f => (U).map f point₀) (distributionMap_inclusion P σ π d)
  have h₂ := Functor.map_comp_apply (U) ((F).map (S₀).distributionInclusion)
    (distributionBaseChart P σ π d).hom point₀
  have h₃ := congrArg ((U).map (distributionBaseChart P σ π d).hom)
    (map_sourcePoint P (S₀).distributionInclusion z₀)
  have h₄ := congrArg (fun v => (U).map (distributionBaseChart P σ π d).hom
    (sourcePoint P ((V) ⨯ ((S₀).algebra.a.2 ⨯ (S₀).algebra.a.2)) v)) hz₀
  refine ⟨(U).map (distributionMap P σ π d) point₀,
    h₀.trans (h₁.trans (h₂.trans (h₃.trans (h₄.trans ?_))))⟩
  have hp := mapped_pair P (Iso.refl ((F).obj (V)))
    (NamedSyntaxComparison.Options.productIso (F)
      (NamedSyntaxComparison.formulaIso P (V) σ π d).symm
      (NamedSyntaxComparison.formulaIso P (V) σ π d).symm)
    (SyntacticNamedHilbert.namePoint x)
    (SyntacticLists.pairPoint 𝗣𝗔 ℕ (SyntacticNamedHilbert.formulaPoint σ π d φ)
      (SyntacticNamedHilbert.formulaPoint σ π d ψ))
  have hq := mapped_pair P (NamedSyntaxComparison.formulaIso P (V) σ π d).symm
    (NamedSyntaxComparison.formulaIso P (V) σ π d).symm
    (SyntacticNamedHilbert.formulaPoint σ π d φ) (SyntacticNamedHilbert.formulaPoint σ π d ψ)
  exact hp.trans (congrArg (pairPoint (namePoint P x)) hq)

theorem hilbertDistribution_point (x : ℕ) (φ ψ : Fm) (h : x ∉ φ.freeVariables) :
    ∃ z : (U).obj (S).distributionParameters,
      (U).map (S).hilbertDistribution z =
        formulaPoint P σ π d (.imp (.all x (.imp φ ψ)) (.imp φ (.all x ψ))) := by
  obtain ⟨z,hz⟩ := distributionPoint_exists P σ π d x φ ψ h
  refine ⟨z,?_⟩
  dsimp only [CategoricalSyntax.hilbertDistribution]
  rw [CategoryTheory.Functor.map_comp_apply,hz]
  apply implication_at P σ π d
  · apply quantifier_at P σ π d
    · exact pairPoint_fst _ _
    · exact ((U).map_comp_apply _ _ _).trans
        ((congrArg ((U).map (S).implicationConstructor)
          (pairPoint_snd _ _)).trans (implication_point P σ π d φ ψ))
  · apply implication_at P σ π d
    · erw [CategoryTheory.Functor.map_comp_apply,pairPoint_snd,pairPoint_fst]
    · apply quantifier_at P σ π d
      · exact pairPoint_fst _ _
      · erw [CategoryTheory.Functor.map_comp_apply,pairPoint_snd,pairPoint_snd]

/-- Both equality instances retain one original body and shared name;
the two success fibers are intersected over those exact coordinates. -/
theorem hilbertEquality_point (x : ℕ) (φ : Fm) (u t : Tm) (ψ χ : Fm)
    (hfu : φ.FreeFor x u) (hft : φ.FreeFor x t)
    (hsu : φ.substitute x u = some ψ) (hst : φ.substitute x t = some χ) :
    ∃ z : (U).obj (S).equalitySchemeParameters,
      (U).map (S).hilbertEquality z =
        formulaPoint P σ π d (.imp (.equal u t) (.imp ψ χ)) := by
  obtain ⟨au,hau,hru⟩ := substitution_instance P σ π d x φ u ψ hfu hsu
  obtain ⟨admissibleT,hat,hrt⟩ := substitution_instance P σ π d x φ t χ hft hst
  let base := pairPoint
    (pairPoint (namePoint P x) (formulaPoint P σ π d φ))
    (pairPoint (termPoint P σ π d u) (termPoint P σ π d t))
  have hinputu : (U).map (S).equalityFirstInput base = substitutionPoint P σ π d x φ u := by
    dsimp only [CategoricalSyntax.equalityFirstInput,substitutionPoint]
    erw [lift_point,lift_point]
    erw [CategoryTheory.Functor.map_comp_apply,pairPoint_fst,pairPoint_snd,
      CategoryTheory.Functor.map_comp_apply,pairPoint_fst,pairPoint_fst,
      CategoryTheory.Functor.map_comp_apply,pairPoint_snd,pairPoint_fst]
  have hinputt : (U).map (S).equalitySecondInput base = substitutionPoint P σ π d x φ t := by
    dsimp only [CategoricalSyntax.equalitySecondInput,substitutionPoint]
    erw [lift_point,lift_point]
    erw [CategoryTheory.Functor.map_comp_apply,pairPoint_fst,pairPoint_snd,
      CategoryTheory.Functor.map_comp_apply,pairPoint_fst,pairPoint_fst,
      CategoryTheory.Functor.map_comp_apply,pairPoint_snd,pairPoint_snd]
  obtain ⟨zu,hzu,hzu'⟩ := pullback_point_exists
    (S).equalityFirstInput (S).admissibleInclusion base au (hinputu.trans hau.symm)
  obtain ⟨zt,hzt,hzt'⟩ := pullback_point_exists
    (S).equalitySecondInput (S).admissibleInclusion base admissibleT (hinputt.trans hat.symm)
  obtain ⟨z,hz,hz'⟩ := pullback_point_exists
    (pullback.fst (S).equalityFirstInput (S).admissibleInclusion)
    (pullback.fst (S).equalitySecondInput (S).admissibleInclusion)
    zu zt (hzu.trans hzt.symm)
  have hb : (U).map (S).equalitySchemeInclusion z = base := by
    exact ((U).map_comp_apply _ _ z).trans
      ((congrArg ((U).map (pullback.fst (S).equalityFirstInput (S).admissibleInclusion)) hz).trans hzu)
  have hu : (U).map (S).equalityFirstAdmissible z = au := by
    exact ((U).map_comp_apply _ _ z).trans
      ((congrArg ((U).map (pullback.snd (S).equalityFirstInput (S).admissibleInclusion)) hz).trans hzu')
  have ht : (U).map (S).equalitySecondAdmissible z = admissibleT := by
    exact ((U).map_comp_apply _ _ z).trans
      ((congrArg ((U).map (pullback.snd (S).equalitySecondInput (S).admissibleInclusion)) hz').trans hzt')
  refine ⟨z,?_⟩
  dsimp only [CategoricalSyntax.hilbertEquality]
  apply implication_at P σ π d
  · calc
      _ = (U).map (S).equalityConstructor
          ((U).map prod.snd ((U).map (S).equalitySchemeInclusion z)) := by
            rw [CategoryTheory.Functor.map_comp_apply,CategoryTheory.Functor.map_comp_apply]
            rfl
      _ = (U).map (S).equalityConstructor
          (pairPoint (termPoint P σ π d u) (termPoint P σ π d t)) :=
            congrArg ((U).map (S).equalityConstructor)
              ((congrArg ((U).map prod.snd) hb).trans (pairPoint_snd _ _))
      _ = _ := equality_point P σ π d u t
  · apply implication_at P σ π d
    · exact ((U).map_comp_apply _ _ z).trans
        ((congrArg ((U).map (S).formulaSubstitution) hu).trans hru)
    · exact ((U).map_comp_apply _ _ z).trans
        ((congrArg ((U).map (S).formulaSubstitution) ht).trans hrt)

end Points
end CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage
