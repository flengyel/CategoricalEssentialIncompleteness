/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonModels
import CategoricalEssentialIncompleteness.V46SyntacticDecidableVariables
import CategoricalEssentialIncompleteness.V46SyntacticDerivationOptionModels

/-! # The actual option object and its literal failure/success chart -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open FailureOfComposition.CodedObjectMembership
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists

namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

abbrev RawOption (C : PredicateCategory T) : PredicateCategory T :=
  PredicateInterpretation.sumCarrier terminalCarrier C

/-- The chosen coproduct is related to literal codes by an actual
isomorphism. No chosen coproduct code is declared to be a native tag. -/
def optionIso (C : PredicateCategory T) : RawOption T C ≅ OptionSyntax.obj C :=
  (PredicateInterpretation.sumIsColimit T terminalCarrier C).coconePointUniqueUpToIso
    (coprodIsCoprod (C := PredicateCategory T) terminalCarrier C) ≪≫
      coprod.mapIso (SyntacticDecidableVariables.terminalIso T) (Iso.refl C)

@[reassoc] theorem sumInl_optionIso (C : PredicateCategory T) :
    representedArrow T (PredicateInterpretation.sumInl T terminalCarrier C) ≫
      (optionIso T C).hom = (SyntacticDecidableVariables.terminalIso T).hom ≫ coprod.inl := by
  change representedArrow T (PredicateInterpretation.sumInl T terminalCarrier C) ≫
    ((PredicateInterpretation.sumIsColimit T terminalCarrier C).coconePointUniqueUpToIso
      (coprodIsCoprod (C := PredicateCategory T) terminalCarrier C)).hom ≫
        coprod.map (SyntacticDecidableVariables.terminalIso T).hom (𝟙 C) = _
  have h := IsColimit.comp_coconePointUniqueUpToIso_hom
    (PredicateInterpretation.sumIsColimit T terminalCarrier C)
    (coprodIsCoprod (C := PredicateCategory T) terminalCarrier C) ⟨WalkingPair.left⟩
  erw [← Category.assoc,h,coprod.inl_map]

@[reassoc] theorem sumInr_optionIso (C : PredicateCategory T) :
    representedArrow T (PredicateInterpretation.sumInr T terminalCarrier C) ≫
      (optionIso T C).hom = (coprod.inr : C ⟶ OptionSyntax.obj C) := by
  change representedArrow T (PredicateInterpretation.sumInr T terminalCarrier C) ≫
    ((PredicateInterpretation.sumIsColimit T terminalCarrier C).coconePointUniqueUpToIso
      (coprodIsCoprod (C := PredicateCategory T) terminalCarrier C)).hom ≫
        coprod.map (SyntacticDecidableVariables.terminalIso T).hom (𝟙 C) = _
  have h := IsColimit.comp_coconePointUniqueUpToIso_hom
    (PredicateInterpretation.sumIsColimit T terminalCarrier C)
    (coprodIsCoprod (C := PredicateCategory T) terminalCarrier C) ⟨WalkingPair.right⟩
  erw [← Category.assoc,h,coprod.inr_map,Category.id_comp]

@[reassoc] theorem inr_optionIso_inv (C : PredicateCategory T) :
    (coprod.inr : C ⟶ OptionSyntax.obj C) ≫ (optionIso T C).inv =
      representedArrow T (PredicateInterpretation.sumInr T terminalCarrier C) := by
  rw [← sumInr_optionIso T C,Category.assoc,Iso.hom_inv_id,Category.comp_id]

@[reassoc] theorem inl_optionIso_inv (C : PredicateCategory T) :
    (coprod.inl : (⊤_ (PredicateCategory T)) ⟶ OptionSyntax.obj C) ≫ (optionIso T C).inv =
      (SyntacticDecidableVariables.terminalIso T).inv ≫
        representedArrow T (PredicateInterpretation.sumInl T terminalCarrier C) := by
  apply (cancel_mono (optionIso T C).hom).mp
  simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id,sumInl_optionIso,
    Iso.inv_hom_id_assoc]

section Models
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]

/-- Every scalar option equation below uses this explicit chart. -/
def optionCode (C : PredicateCategory T) (x : Obj T M (OptionSyntax.obj C)) : M :=
  ((F T M).map (optionIso T C).inv x).val

theorem optionCode_hom (C : PredicateCategory T) (x : Obj T M (RawOption T C)) :
    optionCode T M C ((F T M).map (optionIso T C).hom x) = x.val := by
  unfold optionCode
  rw [← Functor.map_comp_apply,Iso.hom_inv_id,Functor.map_id_apply]

theorem optionCode_injective (C : PredicateCategory T) :
    Function.Injective (optionCode T M C) := by
  intro x y h
  apply ((F T M).mapIso (optionIso T C).symm).toEquiv.injective
  exact Subtype.ext h

variable [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

theorem optionCode_inr (C : PredicateCategory T) (x : Obj T M C) :
    optionCode T M C ((F T M).map (coprod.inr : C ⟶ OptionSyntax.obj C) x) =
      Arithmetic.pair x.val 1 := by
  unfold optionCode
  rw [← Functor.map_comp_apply,inr_optionIso_inv,PredicateInterpretation.map_sumInr]
  rfl

theorem optionCode_inl (C : PredicateCategory T)
    (x : Obj T M (⊤_ (PredicateCategory T))) :
    optionCode T M C ((F T M).map (coprod.inl : (⊤_ (PredicateCategory T)) ⟶ OptionSyntax.obj C) x) = 0 := by
  let y := (F T M).map (SyntacticDecidableVariables.terminalIso T).inv x
  have hy : y.val = 0 := (terminalCarrier_eval y.val).mp y.property
  unfold optionCode
  rw [← Functor.map_comp_apply,inl_optionIso_inv,Functor.map_comp_apply,
    PredicateInterpretation.map_sumInl]
  change Arithmetic.pair y.val 0 = 0
  simp [hy,Arithmetic.pair]

theorem optionCode_fail {X C : PredicateCategory T} (x : Obj T M X) :
    optionCode T M C ((F T M).map (OptionSyntax.fail : X ⟶ OptionSyntax.obj C) x) = 0 := by
  change optionCode T M C ((F T M).map (terminal.from X ≫ coprod.inl) x) = 0
  rw [Functor.map_comp_apply]
  exact optionCode_inl T M C _

theorem optionCode_cases (C : PredicateCategory T) (x : Obj T M (OptionSyntax.obj C)) :
    optionCode T M C x = 0 ∨ ∃ y : Obj T M C,
      (F T M).map (coprod.inr : C ⟶ OptionSyntax.obj C) y = x ∧
        optionCode T M C x = Arithmetic.pair y.val 1 := by
  rcases SyntacticDerivation.OptionModels.sum_cases (F T M)
    (⊤_ (PredicateCategory T)) C x with ⟨a,ha⟩ | ⟨b,hb⟩
  · exact Or.inl (by rw [← ha]; exact optionCode_inl T M C a)
  · exact Or.inr ⟨b,hb,by rw [← hb]; exact optionCode_inr T M C b⟩

theorem optionCode_eq_success_iff (C : PredicateCategory T)
    (x : Obj T M (OptionSyntax.obj C)) (y : Obj T M C) :
    optionCode T M C x = Arithmetic.pair y.val 1 ↔
      x = (F T M).map (coprod.inr : C ⟶ OptionSyntax.obj C) y := by
  constructor
  · intro h
    exact optionCode_injective T M C (h.trans (optionCode_inr T M C y).symm)
  · rintro rfl
    exact optionCode_inr T M C y

theorem optionCode_tag_success (C : PredicateCategory T) (x : Obj T M (OptionSyntax.obj C)) :
    π₂ (optionCode T M C x) = 1 ↔
      ∃ y : Obj T M C, (F T M).map (coprod.inr : C ⟶ OptionSyntax.obj C) y = x := by
  constructor
  · intro h
    rcases optionCode_cases T M C x with hzero | ⟨y,hy,_⟩
    · simp only [hzero,pi₂_zero] at h
      exact (zero_ne_one h).elim
    · exact ⟨y,hy⟩
  · rintro ⟨y,rfl⟩
    rw [optionCode_inr,pi₂_pair]

theorem optionCode_reconstruct (C : PredicateCategory T) (x : Obj T M (OptionSyntax.obj C)) :
    (if π₂ (optionCode T M C x) = 1
      then Arithmetic.pair (π₁ (optionCode T M C x)) 1 else 0) = optionCode T M C x := by
  rcases optionCode_cases T M C x with hzero | ⟨y,_,hcode⟩
  · simp [hzero,pi₂_zero]
  · simp only [hcode,pi₂_pair,↓reduceIte,pi₁_pair]

/-- Functoriality of the option chart uses the actual coproduct map.
The only scalar premise is the already proved value of the component
arrow on its own interpreted points. -/
theorem optionCode_map {C D : PredicateCategory T} (f : C ⟶ D) (φ : M → M)
    (hf : ∀ y : Obj T M C, ((F T M).map f y).val = φ y.val)
    (x : Obj T M (OptionSyntax.obj C)) :
    optionCode T M D ((F T M).map (OptionSyntax.map f) x) =
      if π₂ (optionCode T M C x) = 1
      then Arithmetic.pair (φ (π₁ (optionCode T M C x))) 1 else 0 := by
  rcases SyntacticDerivation.OptionModels.sum_cases (F T M)
    (⊤_ (PredicateCategory T)) C x with ⟨a,ha⟩ | ⟨b,hb⟩
  · rw [← ha]
    have he : (F T M).map (OptionSyntax.map f)
        ((F T M).map (coprod.inl : (⊤_ (PredicateCategory T)) ⟶ OptionSyntax.obj C) a) =
        (F T M).map (coprod.inl : (⊤_ (PredicateCategory T)) ⟶ OptionSyntax.obj D) a := by
      change (F T M).map (coprod.map (𝟙 _) f) ((F T M).map coprod.inl a) = _
      rw [← Functor.map_comp_apply,coprod.inl_map,Category.id_comp]
    rw [he,optionCode_inl T M D a,optionCode_inl T M C a]
    simp [pi₂_zero]
  · rw [← hb]
    have he : (F T M).map (OptionSyntax.map f)
        ((F T M).map (coprod.inr : C ⟶ OptionSyntax.obj C) b) =
        (F T M).map (coprod.inr : D ⟶ OptionSyntax.obj D) ((F T M).map f b) := by
      change (F T M).map (coprod.map (𝟙 _) f) ((F T M).map coprod.inr b) = _
      rw [← Functor.map_comp_apply,coprod.inr_map,Functor.map_comp_apply]
    rw [he,optionCode_inr T M D _,optionCode_inr T M C b]
    simp only [pi₂_pair,↓reduceIte,pi₁_pair]
    exact congrArg (fun y => Arithmetic.pair y 1) (hf b)

theorem optionCode_map_identity {C D : PredicateCategory T} (f : C ⟶ D)
    (hf : ∀ y : Obj T M C, ((F T M).map f y).val = y.val)
    (x : Obj T M (OptionSyntax.obj C)) :
    optionCode T M D ((F T M).map (OptionSyntax.map f) x) = optionCode T M C x := by
  rw [optionCode_map T M f id hf x]
  exact optionCode_reconstruct T M C x

/-- Success of an arbitrary actual option arrow is its actual
pullback fiber. This statement uses preservation of the pullback,
independently of the origin or initiality of that arrow. -/
theorem model_successFiber_iff {C D : PredicateCategory T} (f : C ⟶ OptionSyntax.obj D)
    (q : Obj T M C) :
    (∃ a : Obj T M (pullback f (coprod.inr : D ⟶ OptionSyntax.obj D)),
      (F T M).map (pullback.fst f coprod.inr) a = q) ↔
      π₂ (optionCode T M D ((F T M).map f q)) = 1 := by
  rw [optionCode_tag_success T M D]
  constructor
  · rintro ⟨a,ha⟩
    refine ⟨(F T M).map (pullback.snd f (coprod.inr : D ⟶ OptionSyntax.obj D)) a,?_⟩
    have h := congrArg (fun k => (F T M).map k a)
      (pullback.condition (f := f) (g := (coprod.inr : D ⟶ OptionSyntax.obj D)))
    simpa only [Functor.map_comp_apply,ha] using h.symm
  · rintro ⟨y,hy⟩
    obtain ⟨a,ha,_⟩ := Types.exists_of_isPullback
      ((IsPullback.of_hasPullback f (coprod.inr : D ⟶ OptionSyntax.obj D)).map (F T M)) q y hy.symm
    exact ⟨a,ha⟩

theorem model_successFiber_result {C D : PredicateCategory T} (f : C ⟶ OptionSyntax.obj D)
    (a : Obj T M (pullback f (coprod.inr : D ⟶ OptionSyntax.obj D))) :
    π₁ (optionCode T M D
      ((F T M).map f ((F T M).map (pullback.fst f coprod.inr) a))) =
        ((F T M).map (pullback.snd f (coprod.inr : D ⟶ OptionSyntax.obj D)) a).val := by
  have h := congrArg (fun k => (F T M).map k a)
    (pullback.condition (f := f) (g := (coprod.inr : D ⟶ OptionSyntax.obj D)))
  simp only [Functor.map_comp_apply] at h
  rw [h,optionCode_inr,pi₁_pair]

end Models
end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
