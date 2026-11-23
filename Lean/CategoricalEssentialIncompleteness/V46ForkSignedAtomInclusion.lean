/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ForkDerivationCoordinates
public import CategoricalEssentialIncompleteness.EffectiveForkSpans
public import CategoricalEssentialIncompleteness.V46NumericalForkPartialMaps

/-! # The monomorphism of signed atoms in the fork -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoryTheory.CoprodStruct CategoryTheory.HasCoproducts
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.ForkDerivation
open EffectiveFork (Total)
open ForkSyntax (atomCode negCode atomCode_computable negCode_computable natArrow mem_natArrow)

def codedSum (A B : Total) : Total := ⟨EffectiveFork.coproduct A.obj B.obj⟩
def codedInl (A B : Total) : A ⟶ codedSum A B := ⟨i0 _ _, RestrictionCoproducts.total_i0 _ _⟩
def codedInr (A B : Total) : B ⟶ codedSum A B := ⟨i1 _ _, RestrictionCoproducts.total_i1 _ _⟩

def codedCopair {A B Y : Total} (f : A ⟶ Y) (g : B ⟶ Y) : codedSum A B ⟶ Y :=
  ⟨copair f.hom g.hom, by change rst (copair f.hom g.hom) = 𝟙 (CoprodStruct.coprod A.obj B.obj); rw [restrict_copair, f.property, g.property, coprod_id]⟩

@[simp, reassoc] theorem codedInl_copair {A B Y : Total} (f : A ⟶ Y) (g : B ⟶ Y) :
    codedInl A B ≫ codedCopair f g = f := by
  apply WideSubcategory.hom_ext
  exact i0_copair f.hom g.hom

@[simp, reassoc] theorem codedInr_copair {A B Y : Total} (f : A ⟶ Y) (g : B ⟶ Y) :
    codedInr A B ≫ codedCopair f g = g := by
  apply WideSubcategory.hom_ext
  exact i1_copair f.hom g.hom

def codedSumColimit (A B : Total) : IsColimit (BinaryCofan.mk (codedInl A B) (codedInr A B)) :=
  BinaryCofan.isColimitMk (fun s => codedCopair s.inl s.inr)
    (fun _ => codedInl_copair _ _) (fun _ => codedInr_copair _ _) (by
      intro s m h₁ h₂
      apply WideSubcategory.hom_ext
      apply CategoryTheory.HasCoproducts.hom_ext
      · exact congrArg (fun f => f.hom) (h₁.trans (codedInl_copair s.inl s.inr).symm)
      · exact congrArg (fun f => f.hom) (h₂.trans (codedInr_copair s.inl s.inr).symm))

def sumComparison (A B : Total) : codedSum A B ≅ A ⨿ B :=
  (codedSumColimit A B).coconePointUniqueUpToIso (colimit.isColimit (Limits.pair A B))

@[simp, reassoc] theorem codedInl_comparison (A B : Total) :
    codedInl A B ≫ (sumComparison A B).hom = coprod.inl :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (codedSumColimit A B) (colimit.isColimit (Limits.pair A B)) ⟨.left⟩

@[simp, reassoc] theorem codedInr_comparison (A B : Total) :
    codedInr A B ≫ (sumComparison A B).hom = coprod.inr :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (codedSumColimit A B) (colimit.isColimit (Limits.pair A B)) ⟨.right⟩

open EnumerableCarriers (Carrier val into)
open EffectiveFork (natCarrier)

/-- The tagged input determines its label, even when the two supports overlap. -/
def signedCode (n : ℕ) := if n % 2 = 0 then 3 * (n / 2) else 9 * (n / 2) + 1

theorem signedCode_injective : Function.Injective signedCode := by
  intro x y h
  unfold signedCode at h
  split at h <;> split at h <;> omega

theorem signed_injective (a b : Idem natCarrier) :
    EnumerableCarriers.Injective (copair (into a ≫ natArrow atomCode atomCode_computable)
      (into b ≫ natArrow atomCode atomCode_computable ≫ natArrow negCode negCode_computable)) := by
  let f := into a ≫ natArrow atomCode atomCode_computable
  let g := into b ≫ natArrow atomCode atomCode_computable ≫ natArrow negCode negCode_computable
  have e : copair f g = EnumerableCarriers.copairRaw f g := CategoryTheory.HasCoproducts.hom_ext
    ((i0_copair f g).trans (EnumerableCarriers.inl_copairRaw f g).symm)
    ((i1_copair f g).trans (EnumerableCarriers.inr_copairRaw f g).symm)
  have hg (x y : ℕ) (hy : y ∈ val (copair f g) x) : y = signedCode x := by
    rw [e] at hy
    by_cases he : x % 2 = 0
    · obtain ⟨k, rfl⟩ : ∃ k, x = 2*k := ⟨x/2, by omega⟩
      rw [EnumerableCarriers.val_copair_even] at hy
      obtain ⟨v, hv, hy⟩ := (EnumerableCarriers.mem_val_comp _ _ _ _).mp hy
      have ev := ((EnumerableCarriers.mem_val_idem a k v).mp hv).2
      rw [(mem_natArrow _ _ _ _).mp hy, ev]
      simp [signedCode, atomCode]
    · obtain ⟨k, rfl⟩ : ∃ k, x = 2*k+1 := ⟨x/2, by omega⟩
      rw [EnumerableCarriers.val_copair_odd] at hy
      obtain ⟨v, hv, hw⟩ := (EnumerableCarriers.mem_val_comp _ _ _ _).mp hy
      obtain ⟨u, hu, hz⟩ := (EnumerableCarriers.mem_val_comp _ _ _ _).mp hw
      have ev := ((EnumerableCarriers.mem_val_idem b k v).mp hv).2
      rw [(mem_natArrow _ _ _ _).mp hz, (mem_natArrow _ _ _ _).mp hu, ev]
      simp [signedCode, atomCode, negCode]
      omega
  exact fun x z y hx hz => signedCode_injective ((hg x y hx).symm.trans (hg z y hz))

/-- Monicity of the two actual axiom branches before the three Hilbert schemes are added. -/
theorem signed_atoms_mono (a b : Idem EffectiveFork.V) :
    Mono (coprod.desc (axiomInclusion a ≫ atom) (axiomInclusion b ≫ atom ≫ negation)) := by
  let f := axiomInclusion a ≫ atom
  let g := axiomInclusion b ≫ atom ≫ negation
  have h : Mono (codedCopair f g) := (EffectiveFork.total_mono_iff_injective _).mpr
    ⟨signed_injective (EffectiveFork.centerIdem a) (EffectiveFork.centerIdem b),
     signed_injective (EffectiveFork.leftIdem a) (EffectiveFork.leftIdem b),
     signed_injective (EffectiveFork.rightIdem a) (EffectiveFork.rightIdem b)⟩
  let e := sumComparison (axiomDomain a) (axiomDomain b)
  have he : codedCopair f g = e.hom ≫ coprod.desc f g := by
    apply (codedSumColimit _ _).hom_ext
    rintro ⟨j⟩
    cases j
    · change codedInl _ _ ≫ codedCopair f g = codedInl _ _ ≫ (sumComparison _ _).hom ≫ coprod.desc f g
      rw [← Category.assoc, codedInl_comparison, coprod.inl_desc, codedInl_copair]
    · change codedInr _ _ ≫ codedCopair f g = codedInr _ _ ≫ (sumComparison _ _).hom ≫ coprod.desc f g
      rw [← Category.assoc, codedInr_comparison, coprod.inr_desc, codedInr_copair]
  change Mono (coprod.desc f g)
  have he' : coprod.desc f g = e.inv ≫ codedCopair f g := by rw [he, e.inv_hom_id_assoc]
  rw [he']
  infer_instance

/-- In the literal tuple-diagram category the copair of the two transported
signed constructors is monic for every pair of axiom subdomains. -/
theorem tuple_signed_atoms_mono (a b : Idem EffectiveFork.V) :
    Mono (coprod.desc
      (NumericalForkPartialMaps.totalEquivalence.inverse.map (axiomInclusion a ≫ atom))
      (NumericalForkPartialMaps.totalEquivalence.inverse.map (axiomInclusion b ≫ atom ≫ negation))) := by
  let F := NumericalForkPartialMaps.totalEquivalence.inverse
  let f := axiomInclusion a ≫ atom
  let g := axiomInclusion b ≫ atom ≫ negation
  have : Mono (coprod.desc f g) := signed_atoms_mono a b
  change Mono (coprod.desc (F.map f) (F.map g))
  have eqn : coprod.desc (F.map f) (F.map g) =
      coprodComparison F (axiomDomain a) (axiomDomain b) ≫ F.map (coprod.desc f g) := by
    apply coprod.hom_ext <;> simp [coprodComparison, ← F.map_comp]
  rw [eqn]
  infer_instance

end CategoricalEssentialIncompleteness.V46.ForkDerivation
