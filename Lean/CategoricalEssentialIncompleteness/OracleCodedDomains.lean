/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.OracleDomainRecursion

/-! # Oracle enumerability on coded numerical types -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CategoricalEssentialIncompleteness.LocalConnectedness.OracleComputation

open Encodable

def codedPredicate {α : Type} [Encodable α] (p : α → Prop) (n : ℕ) : Prop :=
  ∃ x,encode x=n ∧ p x

theorem finiteOracleRE_coded {α : Type} [Primcodable α] (S : Set ℕ) (p : α → Prop) :
    FiniteOracleRE S p ↔ FiniteOracleRE S (codedPredicate p) := by
  constructor
  · intro hp
    have he : REPred (fun q : ℕ × α => encode q.2=q.1) :=
      (Primrec.eq.comp (Primrec.encode.comp Primrec.snd) Primrec.fst).computablePred.to_re
    exact ((FiniteOracleRE.of_re he).and (hp.comp Computable.snd)).projection
  · intro hp
    apply (hp.comp Computable.encode).of_eq
    intro x
    constructor
    · rintro ⟨y,hy,hp⟩
      exact (Encodable.encode_injective hy) ▸ hp
    · intro hp
      exact ⟨x,rfl,hp⟩

/-- Relative c.e. membership on an arbitrary coded carrier is compared through
its actual encoding, including exclusion of codes outside that carrier. -/
theorem finiteOracleRE_iff_coded_recursiveIn_domain {α : Type} [Primcodable α]
    (S : Set ℕ) (p : α → Prop) : FiniteOracleRE S p ↔
      ∃ f : ℕ → Part ℕ,Nat.RecursiveIn (oracleSet S) f ∧
        ∀ n,codedPredicate p n ↔ (f n).Dom :=
  (finiteOracleRE_coded S p).trans (finiteOracleRE_iff_recursiveIn_domain S (codedPredicate p))

end CategoricalEssentialIncompleteness.LocalConnectedness.OracleComputation
