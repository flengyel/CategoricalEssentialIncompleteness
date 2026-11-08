/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46MillerSyntaxStep
import CategoricalEssentialIncompleteness.V46MillerUniformTreesEvaluation

/-! # Constructed selected finite records for actual uniform slice operations

The input is the original parameter and postfix word. The initial state
is the empty stack status 1. Every algebra result, including a nullary
result, is obtained at a transition through the actual supplied morphism.
This resource constructs evaluation and proves its graph and totality;
constructor commutation and initiality are separate obligations.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FailureOfComposition.CodedObjectMembership
namespace CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
open SyntacticSyntax SyntacticSyntax.NatVectors
variable {P : Uniform.Family} {R : Total.TotalCategory P} {X Y : Over R}
variable {p q : SyntaxPolynomial (Total.TotalCategory P)}
variable (hT : object R X Y p ⟶ X) (hF : object R X Y q ⟶ Y)

def loopStep (a : UniformTrees.Input) : Part ℕ :=
  valueStep hT hF ((Nat.unpair a.1).1,((nth (V := ℕ)) (Nat.unpair a.1).2 a.2.1,a.2.2))

def loopLength (x : ℕ) : ℕ := len (Nat.unpair x).2

def coefficientWord (x : ℕ) : Prop :=
  (Nat.unpair x).1 ∈ R.obj.support ∧
    ∀ record ∈ Nat.natToList (Nat.unpair x).2,recordValid p q record

theorem loopLength_primrec : Primrec loopLength :=
  NatVectors.len_primrec.comp (Primrec.snd.comp Primrec.unpair)

theorem loopStep_represented :
    Uniform.Represented P (.product .nat (.product .nat .nat)) .nat (loopStep hT hF) := by
  have hc : Computable (fun a : UniformTrees.Input =>
      ((Nat.unpair a.1).1,((nth (V := ℕ)) (Nat.unpair a.1).2 a.2.1,a.2.2))) :=
    (Primrec.pair (Primrec.fst.comp (Primrec.unpair.comp Primrec.fst))
      (Primrec.pair (NatVectors.nth_primrec.comp
        (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst)) (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.snd))).to_comp
  have hk : Uniform.Represented P (.product .nat (.product .nat .nat))
      (.product .nat (.product .nat .nat))
      (fun a : UniformTrees.Input => Part.some
        ((Nat.unpair a.1).1,((nth (V := ℕ)) (Nat.unpair a.1).2 a.2.1,a.2.2))) :=
    Uniform.Represented.of_partrec hc.partrec
  exact (Uniform.Represented.comp hk (valueStep_represented hT hF)).of_eq
    (fun _ => Part.bind_some ..)

theorem coefficientWord_enumerable : Uniform.Enumerable P (coefficientWord (R := R) (p := p) (q := q)) := by
  exact (Uniform.Enumerable.comp (Computable.fst.comp Computable.unpair) R.obj.enumerable).and
    (Uniform.Enumerable.comp (Primrec.nat_natToList.to_comp.comp
      (Computable.snd.comp Computable.unpair)) (recordValid_enumerable p q).listAll)

theorem loopStep_exists {x : ℕ} (hx : coefficientWord (R := R) (p := p) (q := q) x)
    {i : ℕ} (hi : i<loopLength x) {old : ℕ}
    (hold : status R X Y ((Nat.unpair x).1,old)) :
    ∃ new,new ∈ loopStep hT hF (x,(i,old)) ∧ status R X Y ((Nat.unpair x).1,new) := by
  have hil : i<(Nat.natToList (Nat.unpair x).2).length := by
    simpa only [loopLength,NatVectors.len_eq_decode] using hi
  have hm : (nth (V := ℕ)) (Nat.unpair x).2 i ∈ Nat.natToList (Nat.unpair x).2 := by
    rw [NatVectors.nth_eq_decode]
    rw [List.getD_eq_getElem (Nat.natToList (Nat.unpair x).2) 0 hil]
    exact List.getElem_mem hil
  exact valueStep_exists hT hF (Nat.unpair x).1 ((nth (V := ℕ)) (Nat.unpair x).2 i) old (hx.2 _ hm) hold

def evaluation (x : ℕ) : Part ℕ :=
  UniformTrees.run (loopStep hT hF) (fun _ => 1) loopLength x

theorem evaluation_represented : Uniform.Represented P .nat .nat (evaluation hT hF) :=
  UniformTrees.run_represented (loopStep hT hF) (fun _ => 1) loopLength
    (loopStep_represented hT hF) (Computable.const 1) loopLength_primrec.to_comp

theorem evaluation_graph (x s : ℕ) : s ∈ evaluation hT hF x ↔
    ∃ states,UniformTrees.Record (loopStep hT hF) (fun _ => 1) x (loopLength x) states ∧
      states.getD (loopLength x) 0=s :=
  UniformTrees.mem_run (loopStep hT hF) (fun _ => 1) loopLength x s

private theorem initial_status (x : ℕ)
    (hx : coefficientWord (R := R) (p := p) (q := q) x) :
    status R X Y ((Nat.unpair x).1,1) := by
  exact (status_succ R X Y (Nat.unpair x).1 0).mpr ⟨hx.1,fiberStack_nil R X Y _⟩

theorem evaluation_total {x : ℕ}
    (hx : coefficientWord (R := R) (p := p) (q := q) x) : (evaluation hT hF x).Dom := by
  exact UniformTrees.run_total_on (loopStep hT hF) (fun _ => 1) loopLength
    {x | coefficientWord (R := R) (p := p) (q := q) x}
    (fun x _ s => status R X Y ((Nat.unpair x).1,s))
    (fun x hx => initial_status x hx)
    (fun _ hx _ hi _ hs => loopStep_exists hT hF hx hi hs) x hx

theorem evaluation_status {x s : ℕ}
    (hx : coefficientWord (R := R) (p := p) (q := q) x)
    (hs : s ∈ evaluation hT hF x) : status R X Y ((Nat.unpair x).1,s) := by
  exact UniformTrees.run_output_invariant (loopStep hT hF) (fun _ => 1) loopLength
    {x | coefficientWord (R := R) (p := p) (q := q) x}
    (fun x _ s => status R X Y ((Nat.unpair x).1,s))
    (fun x hx => initial_status x hx)
    (fun _ hx _ hi _ hs => loopStep_exists hT hF hx hi hs) hx hs

theorem evaluation_existsUnique {x : ℕ}
    (hx : coefficientWord (R := R) (p := p) (q := q) x) :
    ∃! s,s ∈ evaluation hT hF x ∧ status R X Y ((Nat.unpair x).1,s) := by
  obtain ⟨s,hs⟩ := Part.dom_iff_mem.mp (evaluation_total hT hF hx)
  exact ⟨s,⟨hs,evaluation_status hT hF hx hs⟩,fun _ hs' => Part.mem_unique hs'.1 hs⟩

end CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
