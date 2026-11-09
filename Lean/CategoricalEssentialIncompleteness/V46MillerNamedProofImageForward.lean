import CategoricalEssentialIncompleteness.V46MillerFiniteAxiomProofs
/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46MillerNamedProofImageSchemes
import CategoricalEssentialIncompleteness.V46MillerTotalSubobjectOrder

/-! # Finite native Γ proofs in the actual uniform generated images

Only the existing native relation on finite axiom supports is inducted
on. All target witnesses are constructed with the actual seven schemes,
ordered inference-input pullbacks and original word derivation algebra.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage
open NamedFiniteSyntax NamedPostfixEncoding
open Points
variable (P : Uniform.Family) (σ π : ℕ → Carrier) (d : ℕ)
variable (Γ : Set ℕ) (hΓ : Uniform.Enumerable P (· ∈ Γ))
local notation "U" => Total.underlying (P:=P)
local notation "S" => syntaxData P σ π d
local notation "R" => rules P σ π d Γ hΓ
local notation "A" => proofAlgebra P σ π d Γ hΓ
local notation "c" => conclusion P σ π d Γ hΓ
local notation "Tm" => NamedFiniteSyntax.Term (Symbols σ) d
local notation "Fm" => NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d

abbrev Realizes (φ : (U).obj (S).algebra.a.2) : Prop :=
  ∃ p : (U).obj (proofObject P σ π d Γ hΓ), (U).map (c) p=φ

theorem logical_parameter (p : (U).obj (S).logicalParameters) :
    Realizes P σ π d Γ hΓ ((U).map (S).logicalAxioms p) := by
  let label := (U).map (coprod.inl : (S).logicalParameters ⟶
    (S).logicalParameters ⨿ axiomCarrier P σ π d Γ hΓ) p
  refine ⟨(U).map ((R).nullaryToProof (A)) label,?_⟩
  erw [← CategoryTheory.Functor.map_comp_apply,RulePresentation.nullaryToProof_conclusion]
  change (U).map (coprod.desc (S).logicalAxioms
    (axioms P σ π d Γ hΓ ≫ (S).sentenceInclusion)) ((U).map coprod.inl p)=_
  erw [← CategoryTheory.Functor.map_comp_apply,coprod.inl_desc]

theorem logical_scheme (i : Fin 7)
    (p : (U).obj (SyntacticFiniteNamedSchemes.schemeParameters (S) i)) :
    Realizes P σ π d Γ hΓ ((U).map (SyntacticFiniteNamedSchemes.schemeMorphism (S) i) p) := by
  have h := logical_parameter P σ π d Γ hΓ
    ((U).map (SyntacticFiniteNamedSchemes.schemeInjection (S) i) p)
  rw [← CategoryTheory.Functor.map_comp_apply,SyntacticFiniteNamedSchemes.schemeInjection_formula] at h
  exact h

theorem nonlogical_axiom (p : (U).obj (axiomCarrier P σ π d Γ hΓ)) :
    Realizes P σ π d Γ hΓ ((U).map (axioms P σ π d Γ hΓ ≫ (S).sentenceInclusion) p) := by
  let label := (U).map (coprod.inr : axiomCarrier P σ π d Γ hΓ ⟶
    (S).logicalParameters ⨿ axiomCarrier P σ π d Γ hΓ) p
  refine ⟨(U).map ((R).nullaryToProof (A)) label,?_⟩
  erw [← CategoryTheory.Functor.map_comp_apply,RulePresentation.nullaryToProof_conclusion]
  change (U).map (coprod.desc (S).logicalAxioms
    (axioms P σ π d Γ hΓ ≫ (S).sentenceInclusion)) ((U).map coprod.inr p)=_
  erw [← CategoryTheory.Functor.map_comp_apply,coprod.inr_desc]

/-- The actual unary premise pullback has the supplied child proof. -/
theorem generalization (p : (U).obj ((Syntax.predicateFunctor P).obj (variableCarrier : PredicateCategory 𝗣𝗔) ⨯
      (S).algebra.a.2))
    (h : Realizes P σ π d Γ hΓ ((U).map prod.snd p)) :
    Realizes P σ π d Γ hΓ ((U).map (S).quantifierConstructor p) := by
  obtain ⟨child,hchild⟩ := h
  have hm : (U).map ((R).premises 1) p=
      (U).map (finitePowerMap (c) 1) child := by
    change (U).map prod.snd p=(U).map (c) child
    exact hchild.symm
  obtain ⟨input,hr,_⟩ := pullback_point_exists ((R).premises 1)
    (finitePowerMap (c) 1) p child hm
  refine ⟨(U).map (Derivation.wordConstructor (R) 1) input,?_⟩
  erw [← CategoryTheory.Functor.map_comp_apply,Derivation.wordConstructor_conclusion,
    RulePresentation.ruleConclusion,CategoryTheory.Functor.map_comp_apply,hr]
  rfl

/-- The first child proves φ; the second proves φ⇒ψ. Each is lifted
through the original ordered binary input pullback. -/
theorem modus_ponens (p : (U).obj ((S).algebra.a.2 ⨯ (S).algebra.a.2))
    (hφ : Realizes P σ π d Γ hΓ ((U).map prod.fst p))
    (himp : Realizes P σ π d Γ hΓ ((U).map (S).implicationConstructor p)) :
    Realizes P σ π d Γ hΓ ((U).map prod.snd p) := by
  obtain ⟨child₀,h₀⟩ := hφ
  obtain ⟨child₁,h₁⟩ := himp
  let tuple := pairPoint child₀ child₁
  have hm : (U).map ((R).premises 2) p=
      (U).map (finitePowerMap (c) 2) tuple := by
    apply product_ext
    · change (U).map prod.fst ((U).map (prod.lift prod.fst (S).implicationConstructor) p)=
        (U).map prod.fst ((U).map (prod.map (c) (c)) tuple)
      rw [← CategoryTheory.Functor.map_comp_apply,prod.lift_fst,← CategoryTheory.Functor.map_comp_apply,
        prod.map_fst,CategoryTheory.Functor.map_comp_apply,pairPoint_fst,h₀]
    · change (U).map prod.snd ((U).map (prod.lift prod.fst (S).implicationConstructor) p)=
        (U).map prod.snd ((U).map (prod.map (c) (c)) tuple)
      rw [← CategoryTheory.Functor.map_comp_apply,prod.lift_snd,← CategoryTheory.Functor.map_comp_apply,
        prod.map_snd,CategoryTheory.Functor.map_comp_apply,pairPoint_snd,h₁]
  obtain ⟨input,hr,_⟩ := pullback_point_exists ((R).premises 2)
    (finitePowerMap (c) 2) p tuple hm
  refine ⟨(U).map (Derivation.wordConstructor (R) 2) input,?_⟩
  erw [← CategoryTheory.Functor.map_comp_apply,Derivation.wordConstructor_conclusion,
    RulePresentation.ruleConclusion,CategoryTheory.Functor.map_comp_apply,hr]
  rfl

theorem native_realizes (L : List ℕ) (hL : ∀ x ∈ L,x ∈ Γ) {φ : Fm}
    (h : SyntacticNamedHilbert.Derives σ π d (finiteCarrier L) φ) :
    Realizes P σ π d Γ hΓ (formulaPoint P σ π d φ) := by
  induction h with
  | «axiom» φ he hs =>
      have hφ : formulaCode φ∈Γ := hL _ ((finiteCarrier_eval L _).mp he)
      have h := nonlogical_axiom P σ π d Γ hΓ (axiomPoint P σ π d Γ hΓ φ hs hφ)
      rw [axiomPoint_formula] at h
      exact h
  | one φ ψ =>
      have h := logical_scheme P σ π d Γ hΓ
        0 (pairPoint (formulaPoint P σ π d φ) (formulaPoint P σ π d ψ))
      change Realizes P σ π d Γ hΓ ((U).map (S).hilbertOne _) at h
      rw [hilbertOne_point] at h
      exact h
  | two φ ψ χ =>
      have h := logical_scheme P σ π d Γ hΓ
        1 (pairPoint
          (pairPoint (formulaPoint P σ π d φ) (formulaPoint P σ π d ψ))
          (formulaPoint P σ π d χ))
      change Realizes P σ π d Γ hΓ ((U).map (S).hilbertTwo _) at h
      rw [hilbertTwo_point] at h
      exact h
  | three φ ψ =>
      have h := logical_scheme P σ π d Γ hΓ
        2 (pairPoint (formulaPoint P σ π d φ) (formulaPoint P σ π d ψ))
      change Realizes P σ π d Γ hΓ ((U).map (S).hilbertThree _) at h
      rw [hilbertThree_point] at h
      exact h
  | instantiation x φ t ψ hff hs =>
      obtain ⟨p,hp⟩ := hilbertInstantiation_point P σ π d x φ t ψ hff hs
      have h := logical_scheme P σ π d Γ hΓ 3 p
      change Realizes P σ π d Γ hΓ ((U).map (S).hilbertInstantiation p) at h
      rw [hp] at h
      exact h
  | distribution x φ ψ hx =>
      obtain ⟨p,hp⟩ := hilbertDistribution_point P σ π d x φ ψ hx
      have h := logical_scheme P σ π d Γ hΓ 4 p
      change Realizes P σ π d Γ hΓ ((U).map (S).hilbertDistribution p) at h
      rw [hp] at h
      exact h
  | reflexivity t =>
      have h := logical_scheme P σ π d Γ hΓ
        5 (termPoint P σ π d t)
      change Realizes P σ π d Γ hΓ ((U).map (S).hilbertReflexivity _) at h
      rw [hilbertReflexivity_point] at h
      exact h
  | equality x φ u t ψ χ hfu hft hsu hst =>
      obtain ⟨p,hp⟩ := hilbertEquality_point P σ π d x φ u t ψ χ hfu hft hsu hst
      have h := logical_scheme P σ π d Γ hΓ 6 p
      change Realizes P σ π d Γ hΓ ((U).map (S).hilbertEquality p) at h
      rw [hp] at h
      exact h
  | @generalization x φ h ih =>
      let p := pairPoint (namePoint P x) (formulaPoint P σ π d φ)
      have hp : Realizes P σ π d Γ hΓ ((U).map prod.snd p) := by
        rw [pairPoint_snd]
        exact ih
      have h := generalization P σ π d Γ hΓ p hp
      erw [quantifier_point] at h
      exact h
  | @modusPonens φ ψ hφ himp ihφ ihimp =>
      let p := pairPoint (formulaPoint P σ π d φ) (formulaPoint P σ π d ψ)
      have hp : Realizes P σ π d Γ hΓ ((U).map prod.fst p) := by
        rw [pairPoint_fst]
        exact ihφ
      have hi : Realizes P σ π d Γ hΓ ((U).map (S).implicationConstructor p) := by
        rw [implication_point]
        exact ihimp
      have h := modus_ponens P σ π d Γ hΓ p hp hi
      erw [pairPoint_snd] at h
      exact h


/-- The external Γ set is used only through finite literal axiom supports. -/
theorem finite_realizes {φ : Fm} (h : FiniteAxiomProof σ π d Γ φ) :
    ∃ p : (U).obj (proofObject P σ π d Γ hΓ),
      (U).map (conclusion P σ π d Γ hΓ) p=formulaPoint P σ π d φ := by
  obtain ⟨L,hL,hφ⟩ := h
  exact native_realizes P σ π d Γ hΓ L hL hφ

/-- Membership in the original generated formula range, before choosing
any coordinates on a categorical image object. -/
theorem finite_formula_range {φ : Fm} (h : FiniteAxiomProof σ π d Γ φ) :
    formulaCode φ∈Total.Subobjects.imageCodes (conclusion P σ π d Γ hΓ) := by
  obtain ⟨p,hp⟩ := finite_realizes P σ π d Γ hΓ h
  have hv := (Total.totalFunction_eq_iff (conclusion P σ π d Γ hΓ) p (formulaPoint P σ π d φ)).mp hp
  exact ⟨p.val,formulaPoint_value P σ π d φ ▸ hv⟩

theorem finite_formula_image {φ : Fm} (h : FiniteAxiomProof σ π d Γ φ) :
    formulaCode φ∈Total.Subobjects.imageCodes (image.ι (conclusion P σ π d Γ hΓ)) := by
  rw [Total.Subobjects.imageCodes_image_ι]
  exact finite_formula_range P σ π d Γ hΓ h

/-- Sentence derivations are lifted through the genuine sentence pullback;
its point coordinate is retained and is not identified with the formula word. -/
theorem finite_sentence_realizes {φ : Fm} (h : FiniteAxiomProof σ π d Γ φ)
    (hc : φ.freeVariables=[]) :
    ∃ p : (U).obj (sentenceProofObject P σ π d Γ hΓ),
      (U).map (sentenceConclusion P σ π d Γ hΓ) p=sentencePoint P σ π d φ hc := by
  obtain ⟨p,hp⟩ := finite_realizes P σ π d Γ hΓ h
  have he : (U).map (conclusion P σ π d Γ hΓ) p=
      (U).map (S).sentenceInclusion (sentencePoint P σ π d φ hc) :=
    hp.trans (sentencePoint_inclusion P σ π d φ hc).symm
  obtain ⟨q,_,hq⟩ := pullback_point_exists (conclusion P σ π d Γ hΓ) (S).sentenceInclusion
    p (sentencePoint P σ π d φ hc) he
  exact ⟨q,hq⟩

theorem finite_sentence_range {φ : Fm} (h : FiniteAxiomProof σ π d Γ φ)
    (hc : φ.freeVariables=[]) :
    (sentencePoint P σ π d φ hc).val∈Total.Subobjects.imageCodes (sentenceConclusion P σ π d Γ hΓ) := by
  obtain ⟨p,hp⟩ := finite_sentence_realizes P σ π d Γ hΓ h hc
  exact ⟨p.val,(Total.totalFunction_eq_iff (sentenceConclusion P σ π d Γ hΓ) p _).mp hp⟩

theorem finite_sentence_image {φ : Fm} (h : FiniteAxiomProof σ π d Γ φ)
    (hc : φ.freeVariables=[]) :
    (sentencePoint P σ π d φ hc).val∈Total.Subobjects.imageCodes
      (image.ι (sentenceConclusion P σ π d Γ hΓ)) := by
  rw [Total.Subobjects.imageCodes_image_ι]
  exact finite_sentence_range P σ π d Γ hΓ h hc

/-- Literal formula-word output of the actual sentence conclusion image. -/
theorem finite_sentence_word_range {φ : Fm} (h : FiniteAxiomProof σ π d Γ φ)
    (hc : φ.freeVariables=[]) :
    formulaCode φ∈Total.Subobjects.imageCodes
      (sentenceConclusion P σ π d Γ hΓ ≫ sentenceWord P σ π d) := by
  obtain ⟨p,hp⟩ := finite_sentence_realizes P σ π d Γ hΓ h hc
  refine ⟨p.val,?_⟩
  change formulaCode φ∈Total.val ((sentenceConclusion P σ π d Γ hΓ).hom ≫
    (sentenceWord P σ π d).hom) p.val
  exact (Total.mem_val_comp (sentenceConclusion P σ π d Γ hΓ).hom
    (sentenceWord P σ π d).hom p.val (formulaCode φ)).mpr
      ⟨(sentencePoint P σ π d φ hc).val,
        (Total.totalFunction_eq_iff (sentenceConclusion P σ π d Γ hΓ) p
          (sentencePoint P σ π d φ hc)).mp hp,sentencePoint_word P σ π d φ hc⟩
end CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage
