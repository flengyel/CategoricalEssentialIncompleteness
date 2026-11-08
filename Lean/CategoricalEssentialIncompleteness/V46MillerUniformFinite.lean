import CategoricalEssentialIncompleteness.V46MillerUniformComputations
import CategoricalEssentialIncompleteness.V46MillerFiniteSemidecision

/-! # Positive finite records for the actual uniform oracle families

`Enumerable` already has a proved persistent finite-prefix presentation,
obtained from the actual uniform machine graph characterization. Finite
conjunction takes the maximum of finitely many required prefix lengths.
No oracle is selected and the empty record needs no coefficient inhabitant.
-/
noncomputable section
namespace CategoricalEssentialIncompleteness.V46.Miller.Uniform
open OracleProgram

private theorem common_prefix {α : Type} (Q : α × List ℕ → Prop)
    (hQ : ∀ x l l',l <+: l' → Q (x,l) → Q (x,l'))
    (p : Bits) (L : List α) :
    (∀ x ∈ L,∃ k,Q (x,numericalPrefix p k)) ↔
      ∃ k,∀ x ∈ L,Q (x,numericalPrefix p k) := by
  constructor
  · induction L with
    | nil => exact fun _ => ⟨0,by simp⟩
    | cons x L ih =>
      intro h
      obtain ⟨k,hk⟩ := h x (List.mem_cons_self ..)
      obtain ⟨m,hm⟩ := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
      refine ⟨max k m,?_⟩
      intro y hy
      obtain rfl | hy := List.mem_cons.mp hy
      · exact hQ y _ _ (numericalPrefix_le p (le_max_left k m)) hk
      · exact hQ y _ _ (numericalPrefix_le p (le_max_right k m)) (hm y hy)
  · rintro ⟨k,hk⟩ x hx
    exact ⟨k,hk x hx⟩

namespace Enumerable
variable {P : Family} {α β : Type} [Primcodable α] [Primcodable β]

/-- Semidecide every entry of a finite record, uniformly across all oracles
in the family, retaining empty lists and arbitrary coefficient predicates. -/
theorem listAll {R : α → Prop} (hR : Enumerable P R) :
    Enumerable P (fun L : List α => ∀ x ∈ L,R x) := by
  obtain ⟨Q,hQ,hM,hR⟩ := hR
  have hm : Computable (fun a : List α × List ℕ => a.1.map (fun x => (x,a.2))) :=
    (Primrec.list_map Primrec.fst
      (Primrec.pair Primrec.snd (Primrec.snd.comp Primrec.fst)).to₂).to_comp
  have hfinite : REPred (fun a : List α × List ℕ => ∀ x ∈ a.1,Q (x,a.2)) := by
    apply (REPred.comp hm (FiniteSemidecision.listAll_re hQ)).of_eq
    intro a
    simp
  refine ⟨fun a => ∀ x ∈ a.1,Q (x,a.2),hfinite,?_,?_⟩
  · intro L l l' h hL x hx
    exact hM x l l' h (hL x hx)
  · intro p hp L
    constructor
    · intro h
      exact (common_prefix Q hM p L).mp
        (fun x hx => (hR p hp x).mp (h x hx))
    · rintro ⟨k,hk⟩ x hx
      exact (hR p hp x).mpr ⟨k,hk x hx⟩

/-- The record itself may be computed from an arbitrary numerical input. -/
theorem finiteRecord {R : α → Prop} (hR : Enumerable P R)
    (L : β → List α) (hL : Computable L) :
    Enumerable P (fun b => ∀ x ∈ L b,R x) :=
  Enumerable.comp hL hR.listAll

end Enumerable
end CategoricalEssentialIncompleteness.V46.Miller.Uniform
