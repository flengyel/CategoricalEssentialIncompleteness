/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46MillerOracleProgram

/-! # Effective finite halting cylinders and ordinary input specialization -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Encodable
namespace CategoricalEssentialIncompleteness.V46.Miller.OracleProgram

private theorem execute_table_partrec :
    Partrec (fun a : List ℕ × ℕ => execute (tableOracle a.1) a.2) := by
  have htag : Computable (fun a : List ℕ × ℕ => (Nat.unpair a.2).1) :=
    Computable.fst.comp (Computable.unpair.comp Computable.snd)
  have hpay : Computable (fun a : List ℕ × ℕ => (Nat.unpair a.2).2) :=
    Computable.snd.comp (Computable.unpair.comp Computable.snd)
  have hlookup : Partrec (fun a : (List ℕ × ℕ) × ℕ => tableOracle a.1.1 a.2) :=
    (Computable.list_getElem?.comp
      (Computable.fst.comp Computable.fst) Computable.snd).ofOption
  have hinr : Computable (fun y : ℕ => (Sum.inr y : ℕ ⊕ ℕ)) := Computable.sumInr
  have hread : Partrec₂ (fun a : List ℕ × ℕ => fun k =>
      (tableOracle a.1 k).map (fun b => Sum.inr (Nat.pair (Nat.unpair a.2).2 b))) :=
    (hlookup.map (hinr.comp (Primrec₂.natPair.to_comp.comp
      (hpay.comp (Computable.fst.comp Computable.fst)) Computable.snd)).to₂).to₂
  exact Partrec.nat_casesOn_right htag (Computable.sumInl.comp hpay) hread

private def carry {α : Type} (a : α) (v : ℕ ⊕ ℕ) : ℕ ⊕ (α × ℕ) :=
  v.map id (Prod.mk a)

private theorem carry_computable {α : Type} [Primcodable α] :
    Computable (fun a : α × (ℕ ⊕ ℕ) => carry a.1 a.2) :=
  Computable.sumCasesOn Computable.snd
    (Computable.sumInl.comp Computable.snd).to₂
    (Computable.sumInr.comp (Computable.pair
      (Computable.fst.comp Computable.fst) Computable.snd)).to₂

private theorem fix_carry {α : Type} (f : α → ℕ → Part (ℕ ⊕ ℕ)) (a : α) (s y : ℕ) :
    y ∈ PFun.fix (fun z : α × ℕ => (f z.1 z.2).map (carry z.1)) (a,s) ↔
      y ∈ PFun.fix (f a) s := by
  constructor
  · intro hy
    let C (z : α × ℕ) := ∀ a, z.1 = a → y ∈ PFun.fix (f a) z.2
    have hh : C (a,s) := by
      refine PFun.fixInduction' (C := C) hy ?_ ?_
      · intro z hz a ha
        obtain ⟨v,hv,he⟩ := (Part.mem_map_iff _).mp hz
        cases v with
        | inl t => cases he; subst a; exact PFun.fix_stop hv
        | inr t => cases he
      · intro z z' _ hz ih a ha
        obtain ⟨v,hv,he⟩ := (Part.mem_map_iff _).mp hz
        cases v with
        | inl t => cases he
        | inr t =>
          cases he
          exact PFun.mem_fix_iff.mpr (.inr ⟨t,ha ▸ hv,ih a ha⟩)
    exact hh a rfl
  · intro hy
    refine PFun.fixInduction' (C := fun t => y ∈ PFun.fix
      (fun z : α × ℕ => (f z.1 z.2).map (carry z.1)) (a,t)) hy ?_ ?_
    · intro s hs
      exact PFun.fix_stop ((Part.mem_map_iff _).mpr ⟨.inl y,hs,rfl⟩)
    · intro s s' _ hs ih
      exact PFun.mem_fix_iff.mpr (.inr ⟨(a,s'),
        (Part.mem_map_iff _).mpr ⟨.inr s',hs,rfl⟩,ih⟩)

/-- Joint ordinary partial recursiveness in transition code, finite oracle
word, and numerical input. This is independent of an infinite oracle. -/
theorem finiteEval_partrec :
    Partrec (fun a : (Code × List ℕ) × ℕ => finiteEval a.1.1 a.1.2 a.2) := by
  let Params := (Code × List ℕ) × ℕ
  have he : Partrec (fun a : Params × ℕ => a.1.1.1.eval (Nat.pair a.1.2 a.2)) :=
    Nat.Partrec.Code.eval_part.comp
      (Computable.fst.comp (Computable.fst.comp Computable.fst))
      (Primrec₂.natPair.to_comp.comp
        (Computable.snd.comp Computable.fst) Computable.snd)
  have hstep : Partrec (fun a : Params × ℕ =>
      step a.1.1.1 (tableOracle a.1.1.2) a.1.2 a.2) :=
    he.bind (execute_table_partrec.comp (Computable.pair
      (Computable.snd.comp (Computable.fst.comp (Computable.fst.comp Computable.fst)))
      Computable.snd)).to₂
  have hcarry : Partrec (fun a : Params × ℕ =>
      (step a.1.1.1 (tableOracle a.1.1.2) a.1.2 a.2).map (carry a.1)) :=
    hstep.map (carry_computable.comp (Computable.pair
      (Computable.fst.comp Computable.fst) Computable.snd)).to₂
  have hfix := hcarry.fix.comp (Computable.pair Computable.id (Computable.const 0))
  apply hfix.of_eq
  intro a
  apply Part.ext
  intro y
  exact fix_carry (fun a : Params => step a.1.1 (tableOracle a.1.2) a.2) a 0 y

/-- The uniformly enumerable finite halting certificate. No oracle appears
in this ordinary c.e. predicate. -/
def HaltingCylinder (a : ((Code × ℕ) × ℕ) × Word) : Prop :=
  a.1.2 ∈ finiteEval a.1.1.1 (a.2.map Fin.val) a.1.1.2

private theorem partial_graph_re {α : Type} [Primcodable α]
    (f : α → Part ℕ) (hf : Partrec f) (y : α → ℕ) (hy : Computable y) :
    REPred (fun a => y a ∈ f a) := by
  have hnat : Computable (fun q : ℕ × ℕ => decide (q.1 = q.2)) :=
    (show PrimrecPred (fun q : ℕ × ℕ => q.1 = q.2) from Primrec.eq).computablePred.decide
  have heq : Computable (fun a : α × ℕ => decide (y a.1 = a.2)) :=
    hnat.comp (Computable.pair (hy.comp Computable.fst) Computable.snd)
  let check : α × ℕ → Part Unit :=
    fun a => if y a.1 = a.2 then Part.some () else Part.none
  have hcheck : Partrec check :=
    (Partrec.cond heq (Partrec.const' (Part.some ())) Partrec.none).of_eq (fun a => by
      simp only [check,Bool.cond_decide])
  have h := (hf.bind hcheck.to₂).dom_re
  apply h.of_eq
  intro a
  simp only [Part.dom_iff_mem,Part.mem_bind_iff,check]
  constructor
  · rintro ⟨u,b,hb,hh⟩
    split at hh
    next he => exact he.symm ▸ hb
    next => exact False.elim (Part.notMem_none u hh)
  · intro hb
    exact ⟨(),y a,hb,by simp⟩

private theorem word_graph_re
    (f : (Code × List ℕ) × ℕ → Part ℕ) (hf : Partrec f) :
    REPred (fun a : ((Code × ℕ) × ℕ) × Word =>
      a.1.2 ∈ f ((a.1.1.1,a.2.map Fin.val),a.1.1.2)) := by
  let A := ((Code × ℕ) × ℕ) × Word
  have hcode : Computable (fun a : A => a.1.1.1) :=
    Computable.fst.comp (Computable.fst.comp Computable.fst)
  have hnum : Computable (fun a : A => a.1.1.2) :=
    Computable.snd.comp (Computable.fst.comp Computable.fst)
  have hval : Primrec (fun a : Word × Fin 2 => a.2.val) := Primrec.fin_val.comp Primrec.snd
  have hbits : Computable (fun s : Word => s.map Fin.val) :=
    (Primrec.list_map Primrec.id hval.to₂).to_comp
  have hinput : Computable (fun a : A => ((a.1.1.1,a.2.map Fin.val),a.1.1.2)) :=
    Computable.pair (Computable.pair hcode (hbits.comp Computable.snd)) hnum
  have hg : Partrec (fun a : A => f ((a.1.1.1,a.2.map Fin.val),a.1.1.2)) :=
    hf.comp hinput
  exact partial_graph_re _ hg (fun a : A => a.1.2)
    (Computable.snd.comp Computable.fst)


theorem haltingCylinder_re : REPred HaltingCylinder :=
  word_graph_re (fun a => finiteEval a.1.1 a.1.2 a.2) finiteEval_partrec

/-- The finite certificate describes exactly the open halting set. -/
theorem eval_cylinders (e : Code) (p : Bits) (n y : ℕ) :
    y ∈ eval e p n ↔ ∃ s : Word, HaltingCylinder (((e,n),y),s) ∧ p ∈ cylinder s := by
  constructor
  · intro hy
    obtain ⟨k,hk⟩ := (eval_graph e p n y).mp hy
    exact ⟨bitPrefix p k,hk,mem_cylinder_prefix p k⟩
  · rintro ⟨s,hs,hp⟩
    have hh : numericalPrefix p s.length = s.map Fin.val :=
      congrArg (List.map Fin.val) hp
    exact finiteEval_sound e p s.length n y (hh.symm ▸ hs)


theorem halting_isOpen (e : Code) (n y : ℕ) : IsOpen {p : Bits | y ∈ eval e p n} := by
  have he : {p : Bits | y ∈ eval e p n} =
      ⋃ s : Word, ⋃ (_ : HaltingCylinder (((e,n),y),s)), cylinder s := by
    ext p
    simp only [Set.mem_ofPred_eq,Set.mem_iUnion,eval_cylinders,exists_prop]
  rw [he]
  exact isOpen_iUnion (fun s => isOpen_iUnion (fun _ => cylinder_isOpen s))

/-- Ordinary total recursive input specialization. It leaves oracle queries
and all continuation states unchanged. -/
def sectionCode (e : Code) (x : ℕ) : Code :=
  .comp e (.pair (.pair (.const x) .left) .right)

theorem sectionCode_computable : Computable₂ sectionCode :=
  Nat.Partrec.Code.primrec₂_comp.to_comp.comp Computable.fst
    (Nat.Partrec.Code.primrec₂_pair.to_comp.comp
      (Nat.Partrec.Code.primrec₂_pair.to_comp.comp
        (Nat.Partrec.Code.primrec_const.to_comp.comp Computable.snd)
        (Computable.const Nat.Partrec.Code.left)) (Computable.const Nat.Partrec.Code.right))

theorem sectionCode_transition (e : Code) (x n s : ℕ) :
    (sectionCode e x).eval (Nat.pair n s) = e.eval (Nat.pair (Nat.pair x n) s) := by
  simp [sectionCode,Nat.Partrec.Code.eval,Seq.seq]

theorem sectionCode_run (e : Code) (o : Oracle) (x n s : ℕ) :
    run (sectionCode e x) o n s = run e o (Nat.pair x n) s := by
  have he : step (sectionCode e x) o n = step e o (Nat.pair x n) := by
    funext s
    exact congrArg (fun z => z.bind (execute o)) (sectionCode_transition e x n s)
  exact congrArg (fun f => PFun.fix f s) he

theorem sectionCode_eval (e : Code) (x : ℕ) (p : Bits) (n : ℕ) :
    eval (sectionCode e x) p n = eval e p (Nat.pair x n) :=
  sectionCode_run e (oracle p) x n 0

theorem sectionCode_domain (e : Code) (x : ℕ) (p : Bits) (n : ℕ) :
    (eval (sectionCode e x) p n).Dom ↔ (eval e p (Nat.pair x n)).Dom := by
  rw [sectionCode_eval]


private def universalTransition (v : ℕ) : Part ℕ :=
  let n := (Nat.unpair v).1
  let s := (Nat.unpair v).2
  (Denumerable.ofNat Code (Nat.unpair n).1).eval (Nat.pair (Nat.unpair n).2 s)

private theorem universalTransition_partrec : Partrec universalTransition :=
  Nat.Partrec.Code.eval_part.comp
    ((Computable.ofNat Code).comp (Computable.fst.comp
      (Computable.unpair.comp (Computable.fst.comp Computable.unpair))))
    (Primrec₂.natPair.to_comp.comp
      (Computable.snd.comp (Computable.unpair.comp (Computable.fst.comp Computable.unpair)))
      (Computable.snd.comp Computable.unpair))

/-- One universal ORACLE interpreter, implemented by ordinary transition
code. The simulated program number remains part of the numerical input. -/
def universalCode : Code := Classical.choose (Nat.Partrec.Code.exists_code.mp
  (Partrec.nat_iff.mp universalTransition_partrec))

theorem universalCode_transition (e : Code) (n s : ℕ) :
    universalCode.eval (Nat.pair (Nat.pair (encode e) n) s) = e.eval (Nat.pair n s) := by
  rw [universalCode,Classical.choose_spec (Nat.Partrec.Code.exists_code.mp
    (Partrec.nat_iff.mp universalTransition_partrec))]
  simp only [universalTransition,Nat.unpair_pair,Denumerable.ofNat_encode]

theorem universalCode_eval (e : Code) (p : Bits) (n : ℕ) :
    eval universalCode p (Nat.pair (encode e) n) = eval e p n := by
  have he : step universalCode (oracle p) (Nat.pair (encode e) n) = step e (oracle p) n := by
    funext s
    exact congrArg (fun z => z.bind (execute (oracle p))) (universalCode_transition e n s)
  exact congrArg (fun f => PFun.fix f 0) he

/-- Ordinary programs embed without making any oracle query. -/
def ordinaryCode (e : Code) : Code := .pair (.const 0) (.comp e .left)

theorem ordinaryCode_eval (e : Code) (p : Bits) (n : ℕ) :
    eval (ordinaryCode e) p n = e.eval n := by
  have he : ∀ s, step (ordinaryCode e) (oracle p) n s = (e.eval n).map Sum.inl := by
    intro s
    simp [step,ordinaryCode,Nat.Partrec.Code.eval,Seq.seq,execute,Part.bind_map,
      Nat.unpair_pair,Part.bind_some_eq_map]
  apply Part.ext
  intro y
  constructor
  · intro hy
    obtain h | ⟨s,hs,_⟩ := PFun.mem_fix_iff.mp hy
    · rw [he] at h
      obtain ⟨z,hz,hzy⟩ := (Part.mem_map_iff _).mp h
      exact (Sum.inl.inj hzy) ▸ hz
    · rw [he] at hs
      obtain ⟨z,_,hz⟩ := (Part.mem_map_iff _).mp hs
      cases hz
  · intro hy
    exact PFun.fix_stop (by rw [he]; exact (Part.mem_map_iff _).mpr ⟨y,hy,rfl⟩)


/-- The natural-number enumeration used by the manuscript. -/
def numberedEval (d : ℕ) (p : Bits) (n : ℕ) : Part ℕ :=
  eval (Denumerable.ofNat Code d) p n

@[simp] theorem numberedEval_encode (e : Code) (p : Bits) (n : ℕ) :
    numberedEval (encode e) p n = eval e p n := by
  simp only [numberedEval,Denumerable.ofNat_encode]

def specializationIndex (d x : ℕ) : ℕ :=
  encode (sectionCode (Denumerable.ofNat Code d) x)

theorem specializationIndex_computable : Computable₂ specializationIndex :=
  Computable.encode.comp (sectionCode_computable.comp
    ((Computable.ofNat Code).comp Computable.fst) Computable.snd)

theorem specializationIndex_eval (d x : ℕ) (p : Bits) (n : ℕ) :
    numberedEval (specializationIndex d x) p n = numberedEval d p (Nat.pair x n) := by
  simp only [specializationIndex,numberedEval,Denumerable.ofNat_encode]
  exact sectionCode_eval (Denumerable.ofNat Code d) x p n

theorem numberedEval_graph (d : ℕ) (p : Bits) (n y : ℕ) :
    y ∈ numberedEval d p n ↔ ∃ s : Word,
      HaltingCylinder ((((Denumerable.ofNat Code d),n),y),s) ∧ p ∈ cylinder s :=
  eval_cylinders (Denumerable.ofNat Code d) p n y

end CategoricalEssentialIncompleteness.V46.Miller.OracleProgram
