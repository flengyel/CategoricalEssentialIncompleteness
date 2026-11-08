/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46MillerUnanimity
import CategoricalEssentialIncompleteness.OracleDomainNumbering

/-! # Effective finite halting stages for the actual Miller diagonal

These are finite lists of the SAME halting cylinders used by the verified
oracle interpreter. Prefix length and ordinary evaluator fuel are independent
arguments; the diagonal stage revisits every shorter word with increasing
fuel. In particular it does not attempt to evaluate the encoded stage-length
word using only its own length as the computation bound.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Encodable Denumerable
namespace CategoricalEssentialIncompleteness.V46.Miller.Cut

abbrev Code := Nat.Partrec.Code
abbrev CertificateInput := (ℕ × ℕ) × Word

/-- A finite certificate of the literal diagonal computation. -/
def DiagonalCertificate (a : CertificateInput) : Prop :=
  Unanimity.HaltsOn (a.1.1,a.1.1) a.1.2 a.2

theorem diagonalCertificate_re : REPred DiagonalCertificate := by
  have he : Computable (fun a : CertificateInput => ofNat OracleProgram.Code a.1.1) :=
    (Computable.ofNat OracleProgram.Code).comp (Computable.fst.comp Computable.fst)
  have hn : Computable (fun a : CertificateInput => a.1.1) :=
    Computable.fst.comp Computable.fst
  have hm : Computable (fun a : CertificateInput => a.1.2) :=
    Computable.snd.comp Computable.fst
  exact REPred.comp (Computable.pair (Computable.pair (Computable.pair he hn) hm)
    Computable.snd) OracleProgram.haltingCylinder_re

/-- One fixed ORDINARY certificate program is chosen before the diagonal
index, output value, finite word, and fuel are supplied. -/
def certificateCode : Code := Classical.choose
  (LocalConnectedness.OracleComputation.predicate_code diagonalCertificate_re)

theorem certificateCode_spec (a : CertificateInput) :
    (certificateCode.eval (encode a)).Dom ↔ DiagonalCertificate a :=
  Classical.choose_spec (LocalConnectedness.OracleComputation.predicate_code
    diagonalCertificate_re) a

def Accepted (e m : ℕ) (s : Word) (fuel : ℕ) : Prop :=
  FiniteSemidecision.haltsWithin certificateCode ((e,m),s) fuel

instance accepted_decidable (e m : ℕ) (s : Word) (fuel : ℕ) :
    Decidable (Accepted e m s fuel) :=
  inferInstanceAs (Decidable (FiniteSemidecision.haltsWithin certificateCode ((e,m),s) fuel))

theorem accepted_mono (e m : ℕ) (s : Word) {fuel fuel' : ℕ}
    (h : fuel ≤ fuel') : Accepted e m s fuel → Accepted e m s fuel' :=
  FiniteSemidecision.haltsWithin_mono certificateCode ((e,m),s) h

theorem accepted_sound (e m : ℕ) (s : Word) (fuel : ℕ)
    (h : Accepted e m s fuel) : DiagonalCertificate ((e,m),s) := by
  obtain ⟨y,hy⟩ := Option.isSome_iff_exists.mp h
  exact (certificateCode_spec ((e,m),s)).mp
    (Part.dom_iff_mem.mpr ⟨y,Nat.Partrec.Code.evaln_sound hy⟩)

theorem accepted_complete (e m : ℕ) (s : Word)
    (h : DiagonalCertificate ((e,m),s)) : ∃ fuel, Accepted e m s fuel := by
  obtain ⟨y,hy⟩ := Part.dom_iff_mem.mp ((certificateCode_spec ((e,m),s)).mpr h)
  obtain ⟨fuel,hfuel⟩ := Nat.Partrec.Code.evaln_complete.mp hy
  exact ⟨fuel,Option.isSome_iff_exists.mpr ⟨y,hfuel⟩⟩

/-- Explicitly list all binary words up to a given length. The empty word
is included at bound zero. -/
def wordsUpTo (bound : ℕ) : List Word :=
  (List.range (bound+1)).flatMap FiniteCover.words

theorem mem_wordsUpTo (bound : ℕ) (s : Word) :
    s ∈ wordsUpTo bound ↔ s.length ≤ bound := by
  constructor
  · intro h
    obtain ⟨k,hk,hs⟩ := List.mem_flatMap.mp h
    have hlen := FiniteCover.mem_words_length hs
    have hk' : k < bound+1 := List.mem_range.mp hk
    omega
  · intro h
    exact List.mem_flatMap.mpr ⟨s.length,List.mem_range.mpr (by omega),
      FiniteCover.mem_words_of_length rfl⟩

theorem wordsUpTo_primrec : Primrec wordsUpTo :=
  (Primrec.list_flatMap (Primrec.list_range.comp Primrec.succ)
    (FiniteCover.words_primrec.comp Primrec.snd).to₂).of_eq (fun _ => rfl)

/-- Finite positive halting records with separate prefix and fuel bounds. -/
def boundedWords (e m bound fuel : ℕ) : List Word :=
  (wordsUpTo bound).filter (fun s => Accepted e m s fuel)

theorem mem_boundedWords (e m bound fuel : ℕ) (s : Word) :
    s ∈ boundedWords e m bound fuel ↔ s.length ≤ bound ∧ Accepted e m s fuel := by
  simp only [boundedWords,List.mem_filter,mem_wordsUpTo,decide_eq_true_eq]

theorem boundedWords_primrec :
    Primrec (fun a : (ℕ × ℕ) × (ℕ × ℕ) => boundedWords a.1.1 a.1.2 a.2.1 a.2.2) := by
  let A := (ℕ × ℕ) × (ℕ × ℕ)
  have hR : PrimrecRel (fun s : Word => fun a : A => Accepted a.1.1 a.1.2 s a.2.2) :=
    (FiniteSemidecision.haltsWithin_primrec (α := CertificateInput) certificateCode).comp
      (Primrec.pair (Primrec.fst.comp Primrec.snd) Primrec.fst)
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  exact ((PrimrecRel.listFilter hR).comp
    (wordsUpTo_primrec.comp (Primrec.fst.comp Primrec.snd)) Primrec.id).of_eq (fun _ => rfl)

theorem boundedWords_mono (e m : ℕ) {bound bound' fuel fuel' : ℕ}
    (hB : bound ≤ bound') (hF : fuel ≤ fuel') :
    boundedWords e m bound fuel ⊆ boundedWords e m bound' fuel' := by
  intro s hs
  obtain ⟨hbound,haccept⟩ := (mem_boundedWords e m bound fuel s).mp hs
  exact (mem_boundedWords e m bound' fuel' s).mpr
    ⟨hbound.trans hB,accepted_mono e m s hF haccept⟩

def stageWords (e m t : ℕ) : List Word := boundedWords e m t t

theorem stageWords_primrec :
    Primrec (fun a : (ℕ × ℕ) × ℕ => stageWords a.1.1 a.1.2 a.2) :=
  (boundedWords_primrec.comp (Primrec.pair Primrec.fst (Primrec.pair Primrec.snd Primrec.snd))).of_eq
    (fun _ => rfl)

theorem stageWords_mono (e m : ℕ) {t u : ℕ} (h : t ≤ u) :
    stageWords e m t ⊆ stageWords e m u := boundedWords_mono e m h h

theorem stageWords_sound (e m t : ℕ) (s : Word) (hs : s ∈ stageWords e m t) :
    Unanimity.HaltsOn (e,e) m s :=
  accepted_sound e m s t ((mem_boundedWords e m t t s).mp hs).2

/-- Every actual finite halting cylinder appears at some finite stage,
regardless of the magnitude of its encoded input. -/
theorem stageWords_complete (e m : ℕ) (s : Word)
    (h : Unanimity.HaltsOn (e,e) m s) : ∃ t, s ∈ stageWords e m t := by
  obtain ⟨fuel,hfuel⟩ := accepted_complete e m s h
  refine ⟨max s.length fuel,(mem_boundedWords e m _ _ s).mpr ⟨le_max_left _ _,?_⟩⟩
  exact accepted_mono e m s (le_max_right _ _) hfuel

/-- Finite unions here retain the literal ordered binary words. -/
def cylinderUnion (L : List Word) : Set Bits := {p | ∃ s ∈ L, p ∈ cylinder s}

@[simp] theorem cylinderUnion_nil : cylinderUnion [] = ∅ := by
  ext p
  simp [cylinderUnion]

@[simp] theorem cylinderUnion_cons (s : Word) (L : List Word) :
    cylinderUnion (s::L) = cylinder s ∪ cylinderUnion L := by
  ext p
  simp [cylinderUnion]

theorem cylinderUnion_isOpen (L : List Word) : IsOpen (cylinderUnion L) := by
  induction L with
  | nil => simpa only [cylinderUnion_nil] using isOpen_empty
  | cons s L ih => rw [cylinderUnion_cons]; exact (cylinder_isOpen s).union ih

theorem cylinderUnion_isClosed (L : List Word) : IsClosed (cylinderUnion L) := by
  induction L with
  | nil => simpa only [cylinderUnion_nil] using isClosed_empty
  | cons s L ih => rw [cylinderUnion_cons]; exact (cylinder_isClosed s).union ih

/-- The actual increasing finite halting set H_{e,m,t}. -/
def haltingStage (e m t : ℕ) : Set Bits := cylinderUnion (stageWords e m t)

theorem haltingStage_mono (e m : ℕ) {t u : ℕ} (h : t ≤ u) :
    haltingStage e m t ⊆ haltingStage e m u := by
  rintro p ⟨s,hs,hp⟩
  exact ⟨s,stageWords_mono e m h hs,hp⟩

theorem haltingStage_isOpen (e m t : ℕ) : IsOpen (haltingStage e m t) :=
  cylinderUnion_isOpen _

theorem haltingStage_isClosed (e m t : ℕ) : IsClosed (haltingStage e m t) :=
  cylinderUnion_isClosed _

theorem haltingStage_sound (e m t : ℕ) (p : Bits) (hp : p ∈ haltingStage e m t) :
    m ∈ OracleProgram.numberedEval e p e := by
  obtain ⟨s,hs,hps⟩ := hp
  exact (OracleProgram.numberedEval_graph e p e m).mpr
    ⟨s,stageWords_sound e m t s hs,hps⟩

theorem haltingStage_complete (e m : ℕ) (p : Bits)
    (hp : m ∈ OracleProgram.numberedEval e p e) : ∃ t, p ∈ haltingStage e m t := by
  obtain ⟨s,hs,hps⟩ := (OracleProgram.numberedEval_graph e p e m).mp hp
  obtain ⟨t,ht⟩ := stageWords_complete e m s hs
  exact ⟨t,s,ht,hps⟩

theorem mem_halting_union (e m : ℕ) (p : Bits) :
    p ∈ ⋃ t, haltingStage e m t ↔ m ∈ OracleProgram.numberedEval e p e := by
  constructor
  · intro h
    obtain ⟨t,ht⟩ := Set.mem_iUnion.mp h
    exact haltingStage_sound e m t p ht
  · intro h
    obtain ⟨t,ht⟩ := haltingStage_complete e m p h
    exact Set.mem_iUnion.mpr ⟨t,ht⟩

end CategoricalEssentialIncompleteness.V46.Miller.Cut
