/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.OracleFinitePrefixes

/-! # Uniform oracle-domain enumeration and ordinary recursive specialization -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CategoricalEssentialIncompleteness.LocalConnectedness.OracleComputation

open Nat.Partrec (Code)
open Encodable Denumerable

/-- Ordinary semidecision programs consume the numerical input and a finite
initial segment of the oracle. Their domains form a uniform relative enumeration. -/
def oracleDomain (S : Set ℕ) (a x : ℕ) : Prop :=
  ∃ n,(Code.eval (ofNat Code a) (Nat.pair x (encode (oraclePrefix S n)))).Dom

theorem oracleDomain_uniform (S : Set ℕ) :
    FiniteOracleRE S (fun p : ℕ × ℕ => oracleDomain S p.1 p.2) := by
  have he : Partrec (fun p : (ℕ × ℕ) × List ℕ =>
      Code.eval (ofNat Code p.1.1) (Nat.pair p.1.2 (encode p.2))) :=
    Code.eval_part.comp
      ((Computable.ofNat Code).comp (Computable.fst.comp Computable.fst))
      (Primrec₂.natPair.to_comp.comp (Computable.snd.comp Computable.fst)
        (Computable.encode.comp Computable.snd))
  exact finiteOracleRE_of_prefix S he.dom_re

theorem predicate_code {α : Type} [Primcodable α] {Q : α → Prop} (hQ : REPred Q) :
    ∃ c : Code,∀ x,(c.eval (encode x)).Dom ↔ Q x := by
  obtain ⟨c,hc⟩ := Code.exists_code.mp (Partrec.bind_decode₂_iff.mp hQ)
  refine ⟨c,fun x => ?_⟩
  rw [hc]
  dsimp only
  rw [Encodable.encodek₂]
  simp only [Part.coe_some,Part.bind_some]
  change ((Part.assert (Q x) (fun _ => Part.some ())).map encode).Dom ↔ Q x
  simp [Part.assert]

/-- Every finite-query relative semidecision predicate has an index in the
constructed uniform enumeration, with equality of actual domains. -/
theorem oracleDomain_surjective (S : Set ℕ) {p : ℕ → Prop} (hp : FiniteOracleRE S p) :
    ∃ a,∀ x,oracleDomain S a x ↔ p x := by
  obtain ⟨Q,hQ,_,hp⟩ := hp
  obtain ⟨c,hc⟩ := predicate_code hQ
  refine ⟨encode c,fun x => ?_⟩
  change (∃ n,(Code.eval (ofNat Code (encode c))
    (encode (x,oraclePrefix S n))).Dom) ↔ p x
  simp only [Denumerable.ofNat_encode,hc,← hp]

def sectionCode (c : Code) (z : ℕ) : Code :=
  .comp c (.pair (.pair (.const z) .left) .right)

theorem sectionCode_eval (c : Code) (z x w : ℕ) :
    (sectionCode c z).eval (Nat.pair x w)=c.eval (Nat.pair (Nat.pair z x) w) := by
  simp [sectionCode,Code.eval,Code.eval_const,Seq.seq,Nat.unpair_pair]

theorem sectionCode_computable : Computable₂ sectionCode :=
  Code.primrec₂_comp.to_comp.comp Computable.fst
    (Code.primrec₂_pair.to_comp.comp
      (Code.primrec₂_pair.to_comp.comp (Code.primrec_const.to_comp.comp Computable.snd)
        (Computable.const Code.left)) (Computable.const Code.right))

def sectionIndex (a z : ℕ) : ℕ := encode (sectionCode (ofNat Code a) z)

theorem sectionIndex_computable : Computable₂ sectionIndex :=
  Computable.encode.comp₂ (sectionCode_computable.comp
    ((Computable.ofNat Code).comp Computable.fst) Computable.snd)

/-- The compiler inserts a finite parameter numeral and is ordinary recursive,
uniformly for every oracle. No oracle answer is used during specialization. -/
theorem oracleDomain_section (S : Set ℕ) (a z x : ℕ) :
    oracleDomain S (sectionIndex a z) x ↔ oracleDomain S a (Nat.pair z x) := by
  simp only [oracleDomain,sectionIndex,Denumerable.ofNat_encode,sectionCode_eval]

theorem oracleDomain_specialization {α : Type} [Primcodable α]
    (S : Set ℕ) {p : α × ℕ → Prop} (hp : FiniteOracleRE S p) :
    ∃ a : α → ℕ,Computable a ∧ ∀ z x,oracleDomain S (a z) x ↔ p (z,x) := by
  obtain ⟨Q,hQ,_,hp⟩ := hp
  obtain ⟨c,hc⟩ := predicate_code hQ
  refine ⟨fun z => sectionIndex (encode c) (encode z),
    sectionIndex_computable.comp (Computable.const (encode c)) Computable.encode,?_⟩
  intro z x
  rw [oracleDomain_section]
  change (∃ n,(Code.eval (ofNat Code (encode c))
    (encode ((z,x),oraclePrefix S n))).Dom) ↔ p (z,x)
  simp only [Denumerable.ofNat_encode,hc,← hp]

end CategoricalEssentialIncompleteness.LocalConnectedness.OracleComputation
