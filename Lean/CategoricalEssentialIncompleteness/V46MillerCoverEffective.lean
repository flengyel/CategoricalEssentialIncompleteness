/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerCoverSemantics
public import CategoricalEssentialIncompleteness.V46MillerDyadicEffective
public import CategoricalEssentialIncompleteness.V46MillerFiniteSemidecision

/-! # An ordinary semidecision program for successful finite covers -/

@[expose] public section
noncomputable section
open Encodable Denumerable
namespace CategoricalEssentialIncompleteness.V46.Miller.Unanimity

abbrev Config := (Word × Input) × ℕ

/-- All data in this graph are finite: numerical indices, words and
integer separation certificates, plus ordinary finite halting records. -/
theorem good_re : REPred (fun t : Config × Word => Good t.1.1.1 t.1.1.2 t.1.2 t.2) := by
  have ha : Computable (fun t : Config × Word => t.1.1.2) :=
    Computable.snd.comp (Computable.fst.comp Computable.fst)
  have hu : Computable (fun t : Config × Word => t.1.1.1) :=
    Computable.fst.comp (Computable.fst.comp Computable.fst)
  have hm : Computable (fun t : Config × Word => t.1.2) :=
    Computable.snd.comp Computable.fst
  have he : Computable (fun t : Config × Word => ofNat OracleProgram.Code t.1.1.2.1) :=
    (Computable.ofNat OracleProgram.Code).comp (Computable.fst.comp ha)
  have hn : Computable (fun t : Config × Word => t.1.1.2.2) := Computable.snd.comp ha
  have hh : REPred (fun t : Config × Word => HaltsOn t.1.1.2 t.1.2 t.2) :=
    REPred.comp (Computable.pair (Computable.pair (Computable.pair he hn) hm) Computable.snd)
      OracleProgram.haltingCylinder_re
  have hd : REPred (fun t : Config × Word => ∃ n k, ApartAt t.1.1.1 t.2 n k) :=
    REPred.comp (Computable.pair hu Computable.snd) apart_re
  exact hh.or hd

theorem certified_re : REPred (fun t : (Word × Input) × ℕ => Certified t.1.1 t.1.2 t.2) := by
  have hpack : Primrec (fun t : Config × List Word => t.2.map (fun s => (t.1,s))) :=
    Primrec.list_map Primrec.snd
      (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂
  have hall : REPred (fun t : Config × List Word =>
      ∀ s ∈ t.2, Good t.1.1.1 t.1.1.2 t.1.2 s) :=
    (REPred.comp hpack.to_comp (FiniteSemidecision.listAll_re good_re)).of_eq
      (fun t => by simp)
  have hc : REPred (fun t : Config × List Word => FiniteCover.covers t.2 = true) :=
    (Primrec.eq.comp (FiniteCover.covers_primrec.comp Primrec.snd)
      (Primrec.const true)).computablePred.to_re
  exact (hc.and hall).projection

/-- A single ordinary partial recursive table program, constructed from the
proved enumerable functional graph. No infinite oracle is a parameter. -/
theorem table_program :
    ∃ F : List ℕ × ℕ → Part ℕ, Partrec F ∧
      LocalConnectedness.OracleComputation.MonotoneValues F ∧
      ∀ l n m, m ∈ F (l,n) ↔ Certified (normalizeWord l) (Nat.unpair n) m := by
  obtain ⟨G,hG,hgraph⟩ := FiniteSemidecision.functional_graph certified_re
    (fun a m m' => certified_unique a.1 a.2 m m')
  let F : List ℕ × ℕ → Part ℕ := fun t => G (normalizeWord t.1,Nat.unpair t.2)
  have hF : Partrec F := hG.comp (Computable.pair
    (normalizeWord_primrec.to_comp.comp Computable.fst) (Computable.unpair.comp Computable.snd))
  have hFg (l : List ℕ) (n m : ℕ) :
      m ∈ F (l,n) ↔ Certified (normalizeWord l) (Nat.unpair n) m :=
    hgraph _ m
  refine ⟨F,hF,?_,hFg⟩
  intro l l' h x m hm
  apply (hFg l' x m).mpr
  exact certified_mono _ _ (normalizeWord_prefix l l' h) _ m ((hFg l x m).mp hm)

end CategoricalEssentialIncompleteness.V46.Miller.Unanimity
