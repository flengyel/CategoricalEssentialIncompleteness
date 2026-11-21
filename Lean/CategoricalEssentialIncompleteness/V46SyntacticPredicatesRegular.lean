/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticPredicatesLimits

/-! # Regularity from represented witness search -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.SyntacticPredicates

/-- Finite limits and split strong-epi/mono image factorizations give
coequalizers of kernel pairs and pullback-stable regular epimorphisms. -/
theorem regularOfSplitStrongEpis {K : Type*} [Category K] [HasFiniteLimits K]
    [HasStrongEpiMonoFactorisations K]
    (hsplit : ∀ {X Y : K} (f : X ⟶ Y) [StrongEpi f], IsSplitEpi f) : Regular K where
  hasCoequalizer_of_isKernelPair {X Y Z f g₁ g₂} k := by
    let F : StrongEpiMonoFactorisation f :=
      (HasStrongEpiMonoFactorisations.has_fac f).some
    let : IsSplitEpi F.e := hsplit F.e
    have k' : IsKernelPair (F.e ≫ F.m) g₁ g₂ := by rwa [F.fac]
    have ke : IsKernelPair F.e g₁ g₂ := k'.cancel_right_of_mono
    exact ⟨⟨⟨_, ke.toCoequalizer'⟩⟩⟩
  regularEpiIsStableUnderBaseChange :=
    { of_isPullback := by
        intro X Y Y' S f g f' g' sq hg
        let : IsRegularEpi g := hg
        let : IsSplitEpi g := hsplit g
        have hsec : (f ≫ section_ g) ≫ g = 𝟙 X ≫ f := by simp
        let s := sq.lift (f ≫ section_ g) (𝟙 X) hsec
        let : IsSplitEpi g' := IsSplitEpi.mk' ⟨s, sq.lift_snd _ _ hsec⟩
        exact (inferInstance : IsRegularEpi g') }

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

/-- Strong epimorphisms split by selecting witnesses of the image graph. -/
theorem strongEpi_split {C D : PredicateCategory T} (f : C ⟶ D) [StrongEpi f] :
    IsSplitEpi f := by
  let g := chosenGraph T f
  let e := representedArrow T g.corestriction
  let m := representedArrow T (GraphMorphism.inclusion g.imageInclusionProof)
  have hef : e ≫ m = f := g.image_factor.trans (chosenGraph_class T f)
  let : IsSplitEpi e := g.corestriction.isSplitEpi_of_surjective g.corestriction_surjective
  have sq : CommSq e f m (𝟙 D) := ⟨by simpa only [Category.comp_id] using hef⟩
  refine IsSplitEpi.mk' ⟨sq.lift ≫ section_ e, ?_⟩
  calc
    (sq.lift ≫ section_ e) ≫ f = (sq.lift ≫ section_ e) ≫ (e ≫ m) :=
      congrArg (fun k : C ⟶ D => (sq.lift ≫ section_ e) ≫ k) hef.symm
    _ = sq.lift ≫ (section_ e ≫ e) ≫ m := by simp only [Category.assoc]
    _ = sq.lift ≫ m := by simp only [IsSplitEpi.id, Category.id_comp]
    _ = 𝟙 D := sq.fac_right

theorem regularEpi_split {C D : PredicateCategory T} (f : C ⟶ D) [IsRegularEpi f] :
    IsSplitEpi f := strongEpi_split T f

instance predicateRegular : Regular (PredicateCategory T) :=
  regularOfSplitStrongEpis (strongEpi_split T)

/-- Provable surjectivity is exactly categorical regular epimorphy for
an explicit predicate graph. -/
theorem GraphMorphism.regularEpi_iff_surjective {C D : PredicateCategory T}
    (f : GraphMorphism T C D) :
    IsRegularEpi (representedArrow T f) ↔ T ⊢ surjectiveSentence D f.graph := by
  constructor
  · intro hf
    let : IsRegularEpi (representedArrow T f) := hf
    let : IsSplitEpi (representedArrow T f) := regularEpi_split T _
    apply complete.{0} T
    intro M _ _
    rw [models_iff, surjectiveSentence_eval]
    intro y hy
    have h : relation T (section_ (representedArrow T f) ≫ representedArrow T f) M y y := by
      rw [IsSplitEpi.id, relation_id]
      exact ⟨hy, rfl⟩
    obtain ⟨x, _, hxy⟩ := (relation_comp T _ _ M y y).mp h
    exact ⟨x, (relation_class T f M x y).mp hxy⟩
  · intro hs
    let : IsSplitEpi (representedArrow T f) := f.isSplitEpi_of_surjective hs
    infer_instance

/-- The selected section transports through the comparison equivalence and its counit
isomorphisms. -/
theorem totalSplit_strongEpi_split {X Y : TotalSplit T} (f : X ⟶ Y) [StrongEpi f] :
    IsSplitEpi f := by
  let E := predicateEquivalence T
  let a := E.counitIso.app X
  let b := E.counitIso.app Y
  let : IsSplitEpi (E.inverse.map f) := strongEpi_split T (E.inverse.map f)
  have hnat := E.counitIso.hom.naturality f
  change E.functor.map (E.inverse.map f) ≫ b.hom = a.hom ≫ f at hnat
  have h : a.inv ≫ E.functor.map (E.inverse.map f) ≫ b.hom = f := by
    rw [hnat]
    simp only [a.inv_hom_id_assoc]
  rw [← h]
  infer_instance

instance totalSplitRegular : Regular (TotalSplit T) :=
  regularOfSplitStrongEpis (totalSplit_strongEpi_split T)

end CategoricalEssentialIncompleteness.V46.SyntacticPredicates
