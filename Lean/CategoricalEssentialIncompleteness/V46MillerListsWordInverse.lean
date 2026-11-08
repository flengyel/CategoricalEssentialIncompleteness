/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46MillerListsDecoder
import CategoricalEssentialIncompleteness.V46MillerSyntaxUniformInduction

/-! # Both inverse equations for the actual literal list-word translation

The reverse value program is ordinary partial recursive. Its uniform
source guard is retained when it becomes a carrier morphism. Literal
parser induction proves that each accepted word is the encoding of its
decoded list, without assuming syntax initiality or code correctness.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace CategoricalEssentialIncompleteness.V46.Miller.Lists
open SyntacticSyntax SyntacticSyntax.Coding SyntacticSyntax.NatVectors
variable {P : Uniform.Family} (V : Total.Carrier P)

theorem decoded_word (word : ℕ)
    (hw : word ∈ (Syntax.Raw.uniformWords false (polynomial (⟨V⟩ : Total.TotalCategory P)) .unit).support) :
    ∃ n,n ∈ (carrier V).support ∧ n ∈ CodeInverse.decode word ∧ wordOfCode V n=word := by
  let H : Bool → ℕ → Prop := fun formula word => if formula then True else
    ∃ n,n ∈ (carrier V).support ∧ n ∈ CodeInverse.decode word ∧ wordOfCode V n=word
  have hr : ∀ (formula : Bool) (u : ℕ),u ∈
      (Syntax.Raw.carrier (Syntax.Raw.uniformWords false (polynomial (⟨V⟩ : Total.TotalCategory P)) .unit)
        (Syntax.Raw.uniformWords true (polynomial (⟨V⟩ : Total.TotalCategory P)) .unit)
        (if formula then .unit else polynomial (⟨V⟩ : Total.TotalCategory P))).support →
      Syntax.Raw.UniformChildren H (if formula then .unit else polynomial (⟨V⟩ : Total.TotalCategory P)) u →
      H formula (constructor formula (Syntax.Raw.skeleton (if formula then .unit else polynomial (⟨V⟩ : Total.TotalCategory P))) u) := by
    intro formula u hu hc
    cases formula
    · simp only [H,Bool.false_eq_true,ite_false] at hc ⊢
      change _ ∨ _ at hu
      rcases hu with ⟨htag,hunit⟩ | ⟨htag,hcons⟩
      · have hu0 : (Nat.unpair u).1=0 := hunit
        have he : u=Nat.pair 0 0 := by
          simpa only [hu0,htag] using (Nat.pair_unpair u).symm
        subst u
        exact ⟨0,nil_mem V,CodeInverse.decode_nil V,wordOfCode_nil V⟩
      · have hv : (Nat.unpair (Nat.unpair u).1).1 ∈ V.support := hcons.1
        have htail : ∃ n,n ∈ (carrier V).support ∧
            n ∈ CodeInverse.decode (Nat.unpair (Nat.unpair u).1).2 ∧
              wordOfCode V n=(Nat.unpair (Nat.unpair u).1).2 := by
          simpa [H,Syntax.Raw.UniformChildren,polynomial,htag] using hc
        obtain ⟨n,hn,hdecode,hword⟩ := htail
        let head := (Nat.unpair (Nat.unpair u).1).1
        let tail := (Nat.unpair (Nat.unpair u).1).2
        have he : u=Nat.pair (Nat.pair head tail) 1 := by
          calc
            u=Nat.pair (Nat.unpair u).1 (Nat.unpair u).2 := (Nat.pair_unpair u).symm
            _=Nat.pair (Nat.pair head tail) 1 := by simp only [head,tail,Nat.pair_unpair,htag]
        refine ⟨adjoin head n,(adjoin_mem V head n).mpr ⟨hv,hn⟩,?_,?_⟩
        · simpa only [he,consWord,Nat.unpair_pair] using CodeInverse.decode_cons V head tail n hdecode
        · rw [wordOfCode_adjoin,hword]
          simp only [he,consWord,Nat.unpair_pair]
    · trivial
  exact Syntax.Raw.uniform_word_induction (polynomial (⟨V⟩ : Total.TotalCategory P)) .unit H hr false word hw

theorem decode_supported (word value : ℕ)
    (hw : word ∈ (Syntax.Raw.uniformWords false (polynomial (⟨V⟩ : Total.TotalCategory P)) .unit).support)
    (hv : value ∈ CodeInverse.decode word) : value ∈ (carrier V).support ∧ wordOfCode V value=word := by
  obtain ⟨n,hn,hdecode,hword⟩ := decoded_word V word hw
  have he : value=n := Part.mem_unique hv hdecode
  exact he.symm ▸ And.intro hn hword

def inverseValue (word : ℕ) : Part ℕ :=
  Part.assert (word ∈ (Syntax.Raw.uniformWords false (polynomial (⟨V⟩ : Total.TotalCategory P)) .unit).support)
    (fun _ => CodeInverse.decode word)

theorem inverseValue_graph (word value : ℕ) : value ∈ inverseValue V word ↔
    word ∈ (Syntax.Raw.uniformWords false (polynomial (⟨V⟩ : Total.TotalCategory P)) .unit).support ∧
      value ∈ CodeInverse.decode word := by simp only [inverseValue,Part.mem_assert_iff,exists_prop]

theorem inverseValue_represented : Uniform.Represented P .nat .nat (inverseValue V) := by
  have h := Uniform.Represented.comp
    (Uniform.Represented.identityOn .nat
      (Syntax.Raw.uniformWords false (polynomial (⟨V⟩ : Total.TotalCategory P)) .unit).support
      (Syntax.Raw.uniformWords false (polynomial (⟨V⟩ : Total.TotalCategory P)) .unit).enumerable)
    (Uniform.Represented.of_partrec (X := .nat) (Y := .nat) CodeInverse.decode_partrec)
  exact h.of_eq (fun word => by
    apply Part.ext
    intro value
    simp only [Part.mem_bind_iff,Part.mem_assert_iff,Part.mem_some_iff,inverseValue]
    aesop)

def inverseMap : Syntax.Raw.wordObject false (polynomial (⟨V⟩ : Total.TotalCategory P)) .unit ⟶ object V :=
  let k := Total.arrow (inverseValue V) (inverseValue_represented V)
    (fun word value hv => ((inverseValue_graph V word value).mp hv).1)
    (fun word value hv => (decode_supported V word value
      ((inverseValue_graph V word value).mp hv).1 ((inverseValue_graph V word value).mp hv).2).1)
  ⟨k,(Total.total_iff k).mpr (by
    intro word hw
    obtain ⟨n,_,hn,_⟩ := decoded_word V word hw
    exact Part.dom_iff_mem.mpr ⟨n,(inverseValue_graph V word n).mpr ⟨hw,hn⟩⟩)⟩

theorem inverseMap_graph (word value : ℕ) :
    value ∈ Total.val (inverseMap V).hom word ↔
      word ∈ (Syntax.Raw.uniformWords false (polynomial (⟨V⟩ : Total.TotalCategory P)) .unit).support ∧
        value ∈ CodeInverse.decode word := inverseValue_graph V word value

def wordIso : object V ≅ Syntax.Raw.wordObject false (polynomial (⟨V⟩ : Total.TotalCategory P)) .unit where
  hom := wordMap V
  inv := inverseMap V
  hom_inv_id := by
    apply WideSubcategory.hom_ext
    apply Total.val_ext_on_source
    intro n hn
    have hw := wordOfList_mem V (Nat.natToList n) hn
    have hv : n ∈ Total.val ((wordMap V) ≫ inverseMap V).hom n := by
      change n ∈ Total.val ((wordMap V).hom ≫ (inverseMap V).hom) n
      rw [Total.val_comp]
      exact Part.mem_bind_iff.mpr ⟨wordOfCode V n,(wordMap_graph V n _).mpr ⟨hn,rfl⟩,
        (inverseMap_graph V _ n).mpr ⟨hw,CodeInverse.decode_wordOfCode V n⟩⟩
    exact (Part.eq_some_iff.mpr hv).trans
      (Part.eq_some_iff.mpr ((Total.mem_supportIdentity _ n n).mpr ⟨hn,rfl⟩)).symm
  inv_hom_id := by
    apply WideSubcategory.hom_ext
    apply Total.val_ext_on_source
    intro word hw
    obtain ⟨n,hn,hdecode,hword⟩ := decoded_word V word hw
    have hv : word ∈ Total.val ((inverseMap V) ≫ wordMap V).hom word := by
      change word ∈ Total.val ((inverseMap V).hom ≫ (wordMap V).hom) word
      rw [Total.val_comp]
      exact Part.mem_bind_iff.mpr ⟨n,(inverseMap_graph V word n).mpr ⟨hw,hdecode⟩,
        (wordMap_graph V n word).mpr ⟨hn,hword.symm⟩⟩
    exact (Part.eq_some_iff.mpr hv).trans
      (Part.eq_some_iff.mpr ((Total.mem_supportIdentity _ word word).mpr ⟨hw,rfl⟩)).symm

def wordIsoWithParameters (R : Total.TotalCategory P) :
    constantFamily R (object V) ≅
      constantFamily R (Syntax.Raw.wordObject false (polynomial (⟨V⟩ : Total.TotalCategory P)) .unit) :=
  (constantFamilyFunctor R).mapIso (wordIso V)

end CategoricalEssentialIncompleteness.V46.Miller.Lists
