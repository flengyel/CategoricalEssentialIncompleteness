/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerListsFold
public import CategoricalEssentialIncompleteness.V46MillerSyntaxRawComparison
public import CategoricalEssentialIncompleteness.V46MillerSyntaxRawActionGraphs

/-! # The parameterized raw list constructors

A recursive list leaf is its family code pair(r,list), not the bare list coordinate.
The cons constructor proves the shared parameter from the source projection and then
reads that leaf's list coordinate.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace CategoricalEssentialIncompleteness.V46.Miller.Lists
open SyntacticSyntax.NatVectors
variable {P : Uniform.Family}

def fromFunction {R : Total.TotalCategory P} {A B Z : Over R}
    (p : SyntaxPolynomial (Total.TotalCategory P)) (f : ℕ → ℕ) (hf : Computable f)
    (hs : ∀ n,n ∈ (Syntax.Raw.fiberCarrier R A B p).support → f n ∈ Z.left.obj.support)
    (hp : ∀ n,n ∈ (Syntax.Raw.fiberCarrier R A B p).support →
      (Nat.unpair n).1 ∈ Total.val Z.hom.hom (f n)) : Syntax.Raw.object R A B p ⟶ Z :=
  let k : (Syntax.Raw.object R A B p).left ⟶ Z.left :=
    ⟨Total.totalFromFunction f hf hs,Total.totalFromFunction_total _ _ _⟩
  Over.homMk k (by
    apply WideSubcategory.hom_ext
    apply Total.val_ext_on_source
    intro n hn
    have hk : Total.val k.hom n=Part.some (f n) :=
      Part.eq_some_iff.mpr ((Total.mem_totalFromFunction f hf hs n _).mpr ⟨hn,rfl⟩)
    have hz : Total.val Z.hom.hom (f n)=Part.some (Nat.unpair n).1 := Part.eq_some_iff.mpr (hp n hn)
    have hr : Total.val (Syntax.Raw.projection R A B p).hom n=Part.some (Nat.unpair n).1 :=
      Part.eq_some_iff.mpr ((Syntax.Raw.projection_graph R A B p n _).mpr ⟨hn,rfl⟩)
    change Total.val (k.hom ≫ Z.hom.hom) n=Total.val (Syntax.Raw.projection R A B p).hom n
    rw [Total.val_comp,hk,Part.bind_some,hz,hr])

private theorem fromFunction_graph {R : Total.TotalCategory P} {A B Z : Over R}
    (p : SyntaxPolynomial (Total.TotalCategory P)) (f : ℕ → ℕ) (hf : Computable f)
    (hs : ∀ n,n ∈ (Syntax.Raw.fiberCarrier R A B p).support → f n ∈ Z.left.obj.support)
    (hp : ∀ n,n ∈ (Syntax.Raw.fiberCarrier R A B p).support →
      (Nat.unpair n).1 ∈ Total.val Z.hom.hom (f n)) (n m : ℕ) :
    m ∈ Total.val (fromFunction p f hf hs hp).left.hom n ↔
      n ∈ (Syntax.Raw.fiberCarrier R A B p).support ∧ m=f n :=
  Total.mem_totalFromFunction (X := Syntax.Raw.fiberCarrier R A B p) (Y := Z.left.obj) f hf hs n m

def rawNil (R : Total.TotalCategory P) (V : Total.Carrier P) :
    Syntax.Raw.object R (family R V) (family R V) .unit ⟶ family R V :=
  fromFunction .unit id Computable.id (by
    intro n hn
    exact ⟨hn.1,hn.2.symm ▸ nil_mem V⟩) (by
    intro n hn
    exact (Total.mem_partialFst _ _ n _).mpr ⟨⟨hn.1,hn.2.symm ▸ nil_mem V⟩,rfl⟩)

def consCode (n : ℕ) : ℕ := Nat.pair (Nat.unpair n).1
  (adjoin (Nat.unpair (Nat.unpair n).2).1
    (Nat.unpair (Nat.unpair (Nat.unpair n).2).2).2)

theorem consCode_primrec : Primrec consCode :=
  Primrec₂.natPair.comp (Primrec.fst.comp Primrec.unpair)
    (adjoin_primrec.comp
      (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
      (Primrec.snd.comp (Primrec.unpair.comp
        (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))))

def rawCons (R : Total.TotalCategory P) (V : Total.Carrier P) :
    Syntax.Raw.object R (family R V) (family R V)
      (.product (.coefficient (⟨V⟩ : Total.TotalCategory P)) .term) ⟶ family R V :=
  fromFunction _ consCode consCode_primrec.to_comp (by
    intro n hn
    have ht := (Total.mem_partialFst R.obj (carrier V) _ _).mp hn.2
    change (Nat.unpair (consCode n)).1 ∈ R.obj.support ∧
      (Nat.unpair (consCode n)).2 ∈ (carrier V).support
    simp only [consCode,Nat.unpair_pair]
    exact ⟨hn.1.1,(adjoin_mem V _ _).mpr ⟨hn.1.2,ht.1.2⟩⟩) (by
    intro n hn
    apply (Total.mem_partialFst R.obj (carrier V) (consCode n) _).mpr
    change ((Nat.unpair (consCode n)).1 ∈ R.obj.support ∧
      (Nat.unpair (consCode n)).2 ∈ (carrier V).support) ∧ _
    simp only [consCode,Nat.unpair_pair]
    have ht := (Total.mem_partialFst R.obj (carrier V) _ _).mp hn.2
    exact ⟨⟨hn.1.1,(adjoin_mem V _ _).mpr ⟨hn.1.2,ht.1.2⟩⟩,trivial⟩)

theorem rawNil_graph (R : Total.TotalCategory P) (V : Total.Carrier P) (r out : ℕ) :
    out ∈ Total.val (rawNil R V).left.hom (Nat.pair r 0) ↔
      r ∈ R.obj.support ∧ out=Nat.pair r 0 := by
  unfold rawNil
  rw [fromFunction_graph]
  change (Syntax.Raw.fiber R (family R V) (family R V) .unit (Nat.unpair (Nat.pair r 0)) ∧
    out=Nat.pair r 0) ↔ _
  simp only [Syntax.Raw.fiber,Nat.unpair_pair,and_true]

theorem rawCons_graph (R : Total.TotalCategory P) (V : Total.Carrier P) (r head tail out : ℕ) :
    out ∈ Total.val (rawCons R V).left.hom (Nat.pair r (Nat.pair head (Nat.pair r tail))) ↔
      r ∈ R.obj.support ∧ head ∈ V.support ∧ tail ∈ (carrier V).support ∧
        out=Nat.pair r (adjoin head tail) := by
  unfold rawCons
  rw [fromFunction_graph]
  change (Syntax.Raw.fiber R (family R V) (family R V)
    (.product (.coefficient (⟨V⟩ : Total.TotalCategory P)) .term)
      (Nat.unpair (Nat.pair r (Nat.pair head (Nat.pair r tail)))) ∧
        out=consCode (Nat.pair r (Nat.pair head (Nat.pair r tail)))) ↔ _
  simp only [Syntax.Raw.fiber,Nat.unpair_pair,consCode]
  change (((r ∈ R.obj.support ∧ head ∈ V.support) ∧
    r ∈ Total.val (Total.partialFst R.obj (carrier V)) (Nat.pair r tail)) ∧
      out=Nat.pair r (adjoin head tail)) ↔ _
  rw [Total.mem_partialFst]
  change (((r ∈ R.obj.support ∧ head ∈ V.support) ∧
    ((Nat.unpair (Nat.pair r tail)).1 ∈ R.obj.support ∧
      (Nat.unpair (Nat.pair r tail)).2 ∈ (carrier V).support) ∧ _) ∧ _) ↔ _
  simp only [Nat.unpair_pair]
  tauto

theorem rawCons_input (R : Total.TotalCategory P) (V : Total.Carrier P) (n : ℕ)
    (hn : n ∈ (Syntax.Raw.object R (family R V) (family R V)
      (.product (.coefficient (⟨V⟩ : Total.TotalCategory P)) .term)).left.obj.support) :
    ∃ r head tail,r ∈ R.obj.support ∧ head ∈ V.support ∧ tail ∈ (carrier V).support ∧
      n=Nat.pair r (Nat.pair head (Nat.pair r tail)) := by
  have ht := (Total.mem_partialFst R.obj (carrier V) _ _).mp hn.2
  refine ⟨(Nat.unpair n).1,(Nat.unpair (Nat.unpair n).2).1,
    (Nat.unpair (Nat.unpair (Nat.unpair n).2).2).2,hn.1.1,hn.1.2,ht.1.2,?_⟩
  have hc : (Nat.unpair (Nat.unpair n).2).2=
      Nat.pair (Nat.unpair n).1 (Nat.unpair (Nat.unpair (Nat.unpair n).2).2).2 := by
    rw [← ht.2,Nat.pair_unpair]
  rw [← hc,Nat.pair_unpair,Nat.pair_unpair]

end CategoricalEssentialIncompleteness.V46.Miller.Lists
