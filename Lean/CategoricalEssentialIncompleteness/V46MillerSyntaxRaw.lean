/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46MillerTotalExtensive
import CategoricalEssentialIncompleteness.V46CategoricalSyntax

/-! # Actual positive polynomial fibers for arbitrary uniform slice families

Products retain their ordered numerical entries. Sums use Nat.pair(value,tag),
the literal standard arithmetic syntax coding, rather than the parity code
used for a chosen categorical coproduct. The constructor comparison with
that chosen coproduct is a separate proved diagram.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
variable {P : Uniform.Family}

def taggedSum (X Y : Total.Carrier P) : Total.Carrier P where
  support := {n | ((Nat.unpair n).2=0 ∧ (Nat.unpair n).1 ∈ X.support) ∨
    ((Nat.unpair n).2=1 ∧ (Nat.unpair n).1 ∈ Y.support)}
  enumerable :=
    ((Uniform.Enumerable.of_re ((Primrec.eq.comp (Primrec.snd.comp Primrec.unpair) (.const 0)).computablePred.to_re)).and
      (Uniform.Enumerable.comp (Computable.fst.comp Computable.unpair) X.enumerable)).or
    ((Uniform.Enumerable.of_re ((Primrec.eq.comp (Primrec.snd.comp Primrec.unpair) (.const 1)).computablePred.to_re)).and
      (Uniform.Enumerable.comp (Computable.fst.comp Computable.unpair) Y.enumerable))

def carrier (X Y : Total.Carrier P) : SyntaxPolynomial (Total.TotalCategory P) → Total.Carrier P
  | .term => X
  | .formula => Y
  | .coefficient C => C.obj
  | .unit => Total.terminalCarrier
  | .product a b => Total.product (carrier X Y a) (carrier X Y b)
  | .sum a b => taggedSum (carrier X Y a) (carrier X Y b)

variable (R : Total.TotalCategory P) (X Y : Over R)

def fiber : SyntaxPolynomial (Total.TotalCategory P) → ℕ × ℕ → Prop
  | .term,a => a.1 ∈ Total.val X.hom.hom a.2
  | .formula,a => a.1 ∈ Total.val Y.hom.hom a.2
  | .coefficient C,a => a.1 ∈ R.obj.support ∧ a.2 ∈ C.obj.support
  | .unit,a => a.1 ∈ R.obj.support ∧ a.2=0
  | .product a b,u => fiber a (u.1,(Nat.unpair u.2).1) ∧ fiber b (u.1,(Nat.unpair u.2).2)
  | .sum a b,u => ((Nat.unpair u.2).2=0 ∧ fiber a (u.1,(Nat.unpair u.2).1)) ∨
      ((Nat.unpair u.2).2=1 ∧ fiber b (u.1,(Nat.unpair u.2).1))

theorem fiber_enumerable (p : SyntaxPolynomial (Total.TotalCategory P)) : Uniform.Enumerable P (fiber R X Y p) := by
  induction p with
  | term =>
    exact Uniform.Enumerable.comp (f := fun a : ℕ × ℕ => (a.2,a.1))
      (Computable.pair Computable.snd Computable.fst) (Total.graph_enumerable X.hom.hom)
  | formula =>
    exact Uniform.Enumerable.comp (f := fun a : ℕ × ℕ => (a.2,a.1))
      (Computable.pair Computable.snd Computable.fst) (Total.graph_enumerable Y.hom.hom)
  | coefficient C =>
    exact (Uniform.Enumerable.comp Computable.fst R.obj.enumerable).and
      (Uniform.Enumerable.comp Computable.snd C.obj.enumerable)
  | unit =>
    exact (Uniform.Enumerable.comp Computable.fst R.obj.enumerable).and
      (Uniform.Enumerable.of_re ((Primrec.eq.comp Primrec.snd (.const 0)).computablePred.to_re))
  | product a b ia ib =>
    exact (Uniform.Enumerable.comp (Computable.pair Computable.fst
      (Computable.fst.comp (Computable.unpair.comp Computable.snd))) ia).and
      (Uniform.Enumerable.comp (Computable.pair Computable.fst
        (Computable.snd.comp (Computable.unpair.comp Computable.snd))) ib)
  | sum a b ia ib =>
    have hv : Computable (fun z : ℕ × ℕ => (z.1,(Nat.unpair z.2).1)) :=
      Computable.pair Computable.fst (Computable.fst.comp (Computable.unpair.comp Computable.snd))
    have ht : Primrec (fun z : ℕ × ℕ => (Nat.unpair z.2).2) :=
      Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)
    exact ((Uniform.Enumerable.of_re ((Primrec.eq.comp ht (.const 0)).computablePred.to_re)).and
      (Uniform.Enumerable.comp hv ia)).or
      ((Uniform.Enumerable.of_re ((Primrec.eq.comp ht (.const 1)).computablePred.to_re)).and
        (Uniform.Enumerable.comp hv ib))

theorem fiber_parameter (p : SyntaxPolynomial (Total.TotalCategory P)) {r u : ℕ}
    (h : fiber R X Y p (r,u)) : r ∈ R.obj.support := by
  induction p generalizing u with
  | term => exact Total.val_target X.hom.hom u r h
  | formula => exact Total.val_target Y.hom.hom u r h
  | coefficient C => exact h.1
  | unit => exact h.1
  | product a b ia _ => exact ia h.1
  | sum a b ia ib => exact h.elim (fun h => ia h.2) (fun h => ib h.2)

theorem fiber_carrier (p : SyntaxPolynomial (Total.TotalCategory P)) {r u : ℕ}
    (h : fiber R X Y p (r,u)) : u ∈ (carrier X.left.obj Y.left.obj p).support := by
  induction p generalizing u with
  | term => exact Total.val_source X.hom.hom u r h
  | formula => exact Total.val_source Y.hom.hom u r h
  | coefficient C => exact h.2
  | unit => exact h.2
  | product a b ia ib => exact ⟨ia h.1,ib h.2⟩
  | sum a b ia ib =>
    exact h.elim (fun h => .inl ⟨h.1,ia h.2⟩) (fun h => .inr ⟨h.1,ib h.2⟩)

def fiberCarrier (p : SyntaxPolynomial (Total.TotalCategory P)) : Total.Carrier P :=
  ⟨{n | fiber R X Y p (Nat.unpair n)},Uniform.Enumerable.comp (f := Nat.unpair) Computable.unpair (fiber_enumerable R X Y p)⟩

def projection (p : SyntaxPolynomial (Total.TotalCategory P)) : (⟨fiberCarrier R X Y p⟩ : Total.TotalCategory P) ⟶ R :=
  ⟨Total.totalFromFunction (fun n => (Nat.unpair n).1) (Computable.fst.comp Computable.unpair)
    (fun n hn => fiber_parameter R X Y p (r := (Nat.unpair n).1) (u := (Nat.unpair n).2) hn),Total.totalFromFunction_total _ _ _⟩

def object (p : SyntaxPolynomial (Total.TotalCategory P)) : Over R := Over.mk (projection R X Y p)

theorem projection_graph (p : SyntaxPolynomial (Total.TotalCategory P)) (n r : ℕ) :
    r ∈ Total.val (projection R X Y p).hom n ↔
      fiber R X Y p (Nat.unpair n) ∧ r=(Nat.unpair n).1 :=
  Total.mem_totalFromFunction (X := fiberCarrier R X Y p) (Y := R.obj)
    (fun k => (Nat.unpair k).1)
    (Computable.fst.comp Computable.unpair) (fun n hn => fiber_parameter R X Y p (r := (Nat.unpair n).1) (u := (Nat.unpair n).2) hn) n r

def structuralMap (p q : SyntaxPolynomial (Total.TotalCategory P)) (f : ℕ → ℕ) (hf : Computable f)
    (hs : ∀ n,n ∈ (fiberCarrier R X Y p).support → f n ∈ (fiberCarrier R X Y q).support)
    (hp : ∀ n,n ∈ (fiberCarrier R X Y p).support → (Nat.unpair (f n)).1=(Nat.unpair n).1) :
    object R X Y p ⟶ object R X Y q :=
  let l : (object R X Y p).left ⟶ (object R X Y q).left :=
    ⟨Total.totalFromFunction f hf hs,Total.totalFromFunction_total _ _ _⟩
  Over.homMk l (by
    apply WideSubcategory.hom_ext
    apply Total.val_ext_on_source
    intro n hn
    have hl : Total.val l.hom n = Part.some (f n) :=
      Part.eq_some_iff.mpr ((Total.mem_totalFromFunction f hf hs n (f n)).mpr ⟨hn,rfl⟩)
    have hq : Total.val (projection R X Y q).hom (f n) = Part.some ((Nat.unpair (f n)).1) :=
      Part.eq_some_iff.mpr ((projection_graph R X Y q (f n) _).mpr ⟨hs n hn,rfl⟩)
    have hsrc : Total.val (projection R X Y p).hom n = Part.some ((Nat.unpair n).1) :=
      Part.eq_some_iff.mpr ((projection_graph R X Y p n _).mpr ⟨hn,rfl⟩)
    change Total.val (l.hom ≫ (projection R X Y q).hom) n =
      Total.val (projection R X Y p).hom n
    rw [Total.val_comp,hl,Part.bind_some,hq,hsrc,hp n hn])

theorem structuralMap_graph (p q : SyntaxPolynomial (Total.TotalCategory P)) (f : ℕ → ℕ) (hf : Computable f)
    (hs : ∀ n,n ∈ (fiberCarrier R X Y p).support → f n ∈ (fiberCarrier R X Y q).support)
    (hp : ∀ n,n ∈ (fiberCarrier R X Y p).support → (Nat.unpair (f n)).1=(Nat.unpair n).1)
    (n m : ℕ) :
    m ∈ Total.val (structuralMap R X Y p q f hf hs hp).left.hom n ↔
      fiber R X Y p (Nat.unpair n) ∧ m=f n :=
  Total.mem_totalFromFunction f hf hs n m

def productFst (a b : SyntaxPolynomial (Total.TotalCategory P)) : object R X Y (.product a b) ⟶ object R X Y a :=
  structuralMap R X Y (.product a b) a (fun n => Nat.pair (Nat.unpair n).1 (Nat.unpair (Nat.unpair n).2).1)
    (Primrec₂.natPair.to_comp.comp (Computable.fst.comp Computable.unpair)
      (Computable.fst.comp (Computable.unpair.comp (Computable.snd.comp Computable.unpair))))
    (fun n hn => by simpa [fiberCarrier,fiber,Nat.unpair_pair] using hn.1)
    (fun n _ => by simp only [Nat.unpair_pair])

def productSnd (a b : SyntaxPolynomial (Total.TotalCategory P)) : object R X Y (.product a b) ⟶ object R X Y b :=
  structuralMap R X Y (.product a b) b (fun n => Nat.pair (Nat.unpair n).1 (Nat.unpair (Nat.unpair n).2).2)
    (Primrec₂.natPair.to_comp.comp (Computable.fst.comp Computable.unpair)
      (Computable.snd.comp (Computable.unpair.comp (Computable.snd.comp Computable.unpair))))
    (fun n hn => by simpa [fiberCarrier,fiber,Nat.unpair_pair] using hn.2)
    (fun n _ => by simp only [Nat.unpair_pair])

def sumInl (a b : SyntaxPolynomial (Total.TotalCategory P)) : object R X Y a ⟶ object R X Y (.sum a b) :=
  structuralMap R X Y a (.sum a b) (fun n => Nat.pair (Nat.unpair n).1 (Nat.pair (Nat.unpair n).2 0))
    (Primrec₂.natPair.to_comp.comp (Computable.fst.comp Computable.unpair)
      (Primrec₂.natPair.to_comp.comp (Computable.snd.comp Computable.unpair) (Computable.const 0)))
    (fun n hn => by
      change fiber R X Y (.sum a b) (Nat.unpair (Nat.pair (Nat.unpair n).1 (Nat.pair (Nat.unpair n).2 0)))
      simp only [Nat.unpair_pair, fiber]
      exact Or.inl ⟨True.intro,hn⟩)
    (fun n _ => by simp only [Nat.unpair_pair])

def sumInr (a b : SyntaxPolynomial (Total.TotalCategory P)) : object R X Y b ⟶ object R X Y (.sum a b) :=
  structuralMap R X Y b (.sum a b) (fun n => Nat.pair (Nat.unpair n).1 (Nat.pair (Nat.unpair n).2 1))
    (Primrec₂.natPair.to_comp.comp (Computable.fst.comp Computable.unpair)
      (Primrec₂.natPair.to_comp.comp (Computable.snd.comp Computable.unpair) (Computable.const 1)))
    (fun n hn => by
      change fiber R X Y (.sum a b) (Nat.unpair (Nat.pair (Nat.unpair n).1 (Nat.pair (Nat.unpair n).2 1)))
      simp only [Nat.unpair_pair, fiber]
      exact Or.inr ⟨True.intro,hn⟩)
    (fun n _ => by simp only [Nat.unpair_pair])

@[simp] theorem mem_fiberCarrier (p : SyntaxPolynomial (Total.TotalCategory P)) (r u : ℕ) :
    Nat.pair r u ∈ (fiberCarrier R X Y p).support ↔ fiber R X Y p (r,u) := by
  change fiber R X Y p (Nat.unpair (Nat.pair r u)) ↔ _
  rw [Nat.unpair_pair]

@[simp] theorem fiber_product (a b : SyntaxPolynomial (Total.TotalCategory P)) (r u v : ℕ) :
    fiber R X Y (.product a b) (r,Nat.pair u v) ↔
      fiber R X Y a (r,u) ∧ fiber R X Y b (r,v) := by
  simp only [fiber,Nat.unpair_pair]

@[simp] theorem fiber_sum_inl (a b : SyntaxPolynomial (Total.TotalCategory P)) (r u : ℕ) :
    fiber R X Y (.sum a b) (r,Nat.pair u 0) ↔ fiber R X Y a (r,u) := by
  simp [fiber]

@[simp] theorem fiber_sum_inr (a b : SyntaxPolynomial (Total.TotalCategory P)) (r u : ℕ) :
    fiber R X Y (.sum a b) (r,Nat.pair u 1) ↔ fiber R X Y b (r,u) := by
  simp [fiber]

theorem productFst_graph (a b : SyntaxPolynomial (Total.TotalCategory P)) (r u v m : ℕ) :
    m ∈ Total.val (productFst R X Y a b).left.hom (Nat.pair r (Nat.pair u v)) ↔
      fiber R X Y a (r,u) ∧ fiber R X Y b (r,v) ∧ m=Nat.pair r u := by
  simp only [productFst,structuralMap_graph,Nat.unpair_pair,fiber,and_assoc]

theorem productSnd_graph (a b : SyntaxPolynomial (Total.TotalCategory P)) (r u v m : ℕ) :
    m ∈ Total.val (productSnd R X Y a b).left.hom (Nat.pair r (Nat.pair u v)) ↔
      fiber R X Y a (r,u) ∧ fiber R X Y b (r,v) ∧ m=Nat.pair r v := by
  simp only [productSnd,structuralMap_graph,Nat.unpair_pair,fiber,and_assoc]

theorem sumInl_graph (a b : SyntaxPolynomial (Total.TotalCategory P)) (r u m : ℕ) :
    m ∈ Total.val (sumInl R X Y a b).left.hom (Nat.pair r u) ↔
      fiber R X Y a (r,u) ∧ m=Nat.pair r (Nat.pair u 0) := by
  simp only [sumInl,structuralMap_graph,Nat.unpair_pair]

theorem sumInr_graph (a b : SyntaxPolynomial (Total.TotalCategory P)) (r u m : ℕ) :
    m ∈ Total.val (sumInr R X Y a b).left.hom (Nat.pair r u) ↔
      fiber R X Y b (r,u) ∧ m=Nat.pair r (Nat.pair u 1) := by
  simp only [sumInr,structuralMap_graph,Nat.unpair_pair]

end CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
