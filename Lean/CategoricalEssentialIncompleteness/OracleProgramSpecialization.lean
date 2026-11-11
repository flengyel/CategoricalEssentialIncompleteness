/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.OracleHalting

/-! # Ordinary program specialization on arbitrary coded parameter carriers -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CategoricalEssentialIncompleteness.LocalConnectedness.OracleComputation

open Nat.Partrec (Code)
open Encodable Denumerable

theorem ordinary_program_specialization {α : Type} [Primcodable α]
    {f : α × ℕ → Part ℕ} (hf : Partrec f) :
    ∃ e : α → ℕ,Computable e ∧ ∀ z x,ordinaryEval (e z) x=f (z,x) := by
  obtain ⟨c,hc⟩ := Code.exists_code.mp (Partrec.bind_decode₂_iff.mp hf)
  let e : α → ℕ := fun z => encode (Code.curry c (encode z))
  have he : Computable e := Computable.encode.comp
    (Code.primrec₂_curry.to_comp.comp (Computable.const c) Computable.encode)
  refine ⟨e,he,fun z x => ?_⟩
  change Code.eval (ofNat Code (encode (Code.curry c (encode z)))) x=f (z,x)
  rw [Denumerable.ofNat_encode,Code.eval_curry,hc]
  dsimp only
  change ((↑(decode₂ (α × ℕ) (encode (z,x))) : Part (α × ℕ)).bind
    (fun a => (f a).map encode))=f (z,x)
  rw [Encodable.encodek₂]
  simp only [Part.coe_some,Part.bind_some]
  exact Part.map_id' (fun _ => rfl) _

end CategoricalEssentialIncompleteness.LocalConnectedness.OracleComputation
