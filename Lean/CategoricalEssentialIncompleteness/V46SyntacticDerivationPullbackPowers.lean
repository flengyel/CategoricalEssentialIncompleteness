/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46Inference
public import Mathlib.CategoryTheory.Extensive

/-! Pullback geometry of the original finite ordered premise functor. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.SyntacticDerivation.PullbackPowers
variable {D : Type u} [Category.{v} D] [Regular D]

theorem product {P X Y Z P' X' Y' Z' : D}
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    {a' : P' ⟶ X'} {b' : P' ⟶ Y'} {f' : X' ⟶ Z'} {g' : Y' ⟶ Z'}
    (h : IsPullback a b f g) (h' : IsPullback a' b' f' g') :
    IsPullback (prod.map a a') (prod.map b b') (prod.map f f') (prod.map g g') := by
  refine IsPullback.mk' ?_ ?_ ?_
  · rw [prod.map_map, prod.map_map, h.w, h'.w]
  · intro W s t hs ht
    apply prod.hom_ext
    · apply h.hom_ext
      · have he := congrArg (fun k => k ≫ prod.fst) hs
        simpa only [Category.assoc, prod.map_fst] using he
      · have he := congrArg (fun k => k ≫ prod.fst) ht
        simpa only [Category.assoc, prod.map_fst] using he
    · apply h'.hom_ext
      · have he := congrArg (fun k => k ≫ prod.snd) hs
        simpa only [Category.assoc, prod.map_snd] using he
      · have he := congrArg (fun k => k ≫ prod.snd) ht
        simpa only [Category.assoc, prod.map_snd] using he
  · intro W s t hw
    have hw₁ : (s ≫ prod.fst) ≫ f = (t ≫ prod.fst) ≫ g := by
      have he := congrArg (fun k => k ≫ prod.fst) hw
      simpa only [Category.assoc, prod.map_fst] using he
    have hw₂ : (s ≫ prod.snd) ≫ f' = (t ≫ prod.snd) ≫ g' := by
      have he := congrArg (fun k => k ≫ prod.snd) hw
      simpa only [Category.assoc, prod.map_snd] using he
    refine ⟨prod.lift (h.lift _ _ hw₁) (h'.lift _ _ hw₂), ?_, ?_⟩
    · apply prod.hom_ext
      · simp only [Category.assoc, prod.map_fst, prod.lift_fst_assoc, h.lift_fst]
      · simp only [Category.assoc, prod.map_snd, prod.lift_snd_assoc, h'.lift_fst]
    · apply prod.hom_ext
      · simp only [Category.assoc, prod.map_fst, prod.lift_fst_assoc, h.lift_snd]
      · simp only [Category.assoc, prod.map_snd, prod.lift_snd_assoc, h'.lift_snd]

theorem power {P X Y Z : D} {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback a b f g) (n : ℕ) :
    IsPullback (finitePowerMap a n) (finitePowerMap b n)
      (finitePowerMap f n) (finitePowerMap g n) := by
  induction n with
  | zero => exact IsPullback.id_horiz (𝟙 _)
  | succ n ih =>
    cases n with
    | zero => exact h
    | succ n => exact product ih h

theorem fixedProduct (A : D) {P X Y Z : D}
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback a b f g) :
    IsPullback (prod.map (𝟙 A) a) (prod.map (𝟙 A) b)
      (prod.map (𝟙 A) f) (prod.map (𝟙 A) g) :=
  product (IsPullback.id_horiz (𝟙 A)) h

variable [FinitaryExtensive D]

/-- Universal finite sums assemble the component rule pullbacks. -/
theorem finiteSum {I : Type} [Finite I] {P X : I → D} {F Z : D}
    (a : ∀ i, P i ⟶ X i) (b : ∀ i, P i ⟶ F)
    (f : ∀ i, X i ⟶ Z) (g : F ⟶ Z)
    (h : ∀ i, IsPullback (a i) (b i) (f i) g) :
    IsPullback (Sigma.desc (fun i => a i ≫ Sigma.ι X i)) (Sigma.desc b)
      (Sigma.desc f) g := by
  have hu := FinitaryPreExtensive.isUniversal_finiteCoproducts (coproductIsCoproduct X)
  have hp := hu.isPullback_of_isColimit_left f (Sigma.desc f) g b a
    (fun i => (h i).flip) (coproductIsCoproduct P)
  have hd {Y : D} (k : ∀ i, P i ⟶ Y) :
      Cofan.IsColimit.desc (coproductIsCoproduct P) k = Sigma.desc k := by
    apply Sigma.hom_ext
    intro i
    calc
      _ = k i := Cofan.IsColimit.fac (coproductIsCoproduct P) k i
      _ = _ := (Sigma.ι_comp_desc k i).symm
  simpa only [hd, Cofan.mk_pt, cofan_mk_inj] using hp.flip

end CategoricalEssentialIncompleteness.V46.SyntacticDerivation.PullbackPowers
