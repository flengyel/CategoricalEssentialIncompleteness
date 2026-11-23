/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import Mathlib.Computability.Reduce
public import CategoricalEssentialIncompleteness.V46JaniczakFOLCoding
public import CategoricalEssentialIncompleteness.V46JaniczakNativeSyntax
public import CategoricalEssentialIncompleteness.V46JaniczakAxiomEnumeration

/-! # Recursive axiomatizability and extensions in the ordinary first-order language -/

@[expose] public section

set_option autoImplicit false

open FFL FFL.FirstOrder FFL.Entailment Encodable
namespace Janiczak.FOL

def TheoremWords (U : Theory L) : Set ℕ :=
  {w | ∃ σ : Sentence L, encode σ = w ∧ U ⊢ σ}

def EssentiallyUndecidable (T : Theory L) :=
  ∀ U : Theory L, T ⊆ U → Entailment.Consistent U → ¬ ComputablePred (· ∈ TheoremWords U)

theorem theorem_word (U : Theory L) (φ : Sentence L) :
    encode φ ∈ TheoremWords U ↔ U ⊢ φ := by
  constructor
  · rintro ⟨ψ,h,hψ⟩
    exact Encodable.encode_inj.mp h ▸ hψ
  · exact fun h => ⟨φ,rfl,h⟩

private theorem incompatible {T : Set Janiczak.Formula} {U : Theory L}
    (incl : theory T ⊆ U) (hc : Entailment.Consistent U)
    (p : Janiczak.Formula) (hp : U ⊢ sentence p) (hn : U ⊢ sentence p.neg) : False := by
  apply consistent_iff_unprovable_bot.mp hc
  let _ : 𝗘𝗤 L ⪯ U := Theory.Proof.weakerThan_of_le (Set.Subset.trans
    (show 𝗘𝗤 L ⊆ theory T from Set.subset_union_left) incl)
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ hm
  have hp' := (sentence_models p).mp (consequence_iff.mp (Theory.Proof.sound hp) M hm)
  have hn' := (sentence_models p.neg).mp (consequence_iff.mp (Theory.Proof.sound hn) M hm)
  let v : ℕ → M := fun _ => Classical.choice (inferInstance : Nonempty M)
  exact (hn' v (hp' v)).elim

theorem essentiallyUndecidable_of_inseparable {P N : Set ℕ}
    (h : CategoricalEssentialIncompleteness.Numerical.RecursivelyInseparable P N) :
    EssentiallyUndecidable (theory (Signed P N)) := by
  intro U incl hc decideU
  let A := Formula.sizeSentence
  let D : Set ℕ := {i | U ⊢ sentence (A i)}
  have effective : Computable (fun i => encode (sentence (A i))) :=
    (Coding.forward_primrec.to_comp.comp Formula.primrec_sizeSentence.to_comp).of_eq
      (fun i => Coding.forward_code (A i))
  apply h.2
  refine ⟨D, ComputablePred.computable_of_manyOneReducible ⟨_,effective,fun i => (theorem_word U _).symm⟩ decideU, ?_, ?_⟩
  · intro i hi
    exact by_axm (incl (Or.inr ⟨A i,.pos hi,rfl⟩))
  · apply Set.disjoint_left.mpr
    intro i
    exact fun hi hn => incompatible incl hc (A i) hi
      (by_axm (incl (Or.inr ⟨(A i).neg,.neg hn,rfl⟩)))

private theorem logic_words_enumerable : REPred (fun w : ℕ => w ∈ encode '' (𝗘𝗤 L)) := by
  let codes := [encode (Theory.Eq.refl L),encode (Theory.Eq.symm L),encode (Theory.Eq.trans L),
    encode (Theory.Eq.relExt (L := L) Language.Set.Rel.eq),
    encode (Theory.Eq.relExt (L := L) Language.Set.Rel.mem)]
  have he : ∀ w : ℕ, w ∈ codes ↔ w ∈ encode '' (𝗘𝗤 L) := by
    intro w
    constructor
    · intro hw
      simp only [codes,List.mem_cons,List.mem_nil_iff,or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl
      · exact ⟨_,.refl,rfl⟩
      · exact ⟨_,.symm,rfl⟩
      · exact ⟨_,.trans,rfl⟩
      · exact ⟨_,.relExt _,rfl⟩
      · exact ⟨_,.relExt _,rfl⟩
    · rintro ⟨φ,hφ,rfl⟩
      cases hφ with
      | refl => simp [codes]
      | symm => simp [codes]
      | trans => simp [codes]
      | funcExt f => exact Empty.elim f
      | relExt r => cases r <;> simp [codes]
  have hm : PrimrecPred (fun w : ℕ => ∃ n ∈ codes, n = w) :=
    Primrec.eq.exists_mem_list.comp (Primrec.const codes) Primrec.id
  exact hm.computablePred.to_re.of_eq (fun w => (by simp : (∃ n ∈ codes, n = w) ↔ w ∈ codes) |>.trans (he w))

theorem signed_axiom_words_enumerable {P N : Set ℕ} (hP : REPred (· ∈ P)) (hN : REPred (· ∈ N)) :
    REPred (fun w : ℕ => w ∈ encode '' theory (Signed P N)) := by
  have hw := Janiczak.enumerable_image (Janiczak.signed_axioms_enumerable hP hN)
    Coding.forward Coding.forward_primrec.to_comp
  apply (logic_words_enumerable.or hw).of_eq
  intro w
  constructor
  · rintro (⟨φ,hφ,rfl⟩ | ⟨i,⟨p,hp,rfl⟩,hw⟩)
    · exact ⟨φ,Or.inl hφ,rfl⟩
    · exact ⟨sentence p,Or.inr ⟨p,hp,rfl⟩,(Coding.forward_code p).symm.trans hw⟩
  · rintro ⟨φ,(hφ | ⟨p,hp,rfl⟩),rfl⟩
    · exact Or.inl ⟨φ,hφ,rfl⟩
    · exact Or.inr ⟨p.code,⟨p,hp,rfl⟩,Coding.forward_code p⟩

end Janiczak.FOL
