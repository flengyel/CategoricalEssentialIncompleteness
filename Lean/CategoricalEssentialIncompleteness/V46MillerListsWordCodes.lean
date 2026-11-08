/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46MillerListsCarrier
import CategoricalEssentialIncompleteness.V46MillerSyntaxCarrierConstructors
import CategoricalEssentialIncompleteness.V46MillerSyntaxUniformAlgebra

/-! # Literal constructor-preserving list-to-word code translation

This is an ordinary primitive-recursive code translation. It retains
the original label and ordered tail. Membership of an arbitrary uniform
coefficient carrier is a positive support condition, not a code field.
The inverse word translation and its comparison are separate obligations.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace CategoricalEssentialIncompleteness.V46.Miller.Lists
open SyntacticSyntax SyntacticSyntax.Coding SyntacticSyntax.NatVectors
variable {P : Uniform.Family} (V : Total.Carrier P)

def nilWord : ℕ := constructor false (Syntax.Raw.skeleton (polynomial (⟨V⟩ : Total.TotalCategory P))) (Nat.pair 0 0)

def consWord (v tail : ℕ) : ℕ :=
  constructor false (Syntax.Raw.skeleton (polynomial (⟨V⟩ : Total.TotalCategory P)))
    (Nat.pair (Nat.pair v tail) 1)

def wordOfList (L : List ℕ) : ℕ := L.foldr (consWord V) (nilWord V)

@[simp] theorem wordOfList_nil : wordOfList V []=nilWord V := rfl
@[simp] theorem wordOfList_cons (v : ℕ) (L : List ℕ) :
    wordOfList V (v::L)=consWord V v (wordOfList V L) := rfl

theorem consWord_primrec : Primrec₂ (consWord V) :=
  (NatVectors.constructor_primrec false (Syntax.Raw.skeleton (polynomial (⟨V⟩ : Total.TotalCategory P)))).comp
    (Primrec₂.natPair.comp (Primrec₂.natPair.comp Primrec.fst Primrec.snd) (.const 1))

theorem wordOfList_primrec : Primrec (wordOfList V) := by
  have hs : Primrec₂ (fun (_ : List ℕ) (p : ℕ × ℕ) => consWord V p.1 p.2) :=
    Primrec.to₂ ((consWord_primrec V).comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
  exact Primrec.of_eq (Primrec.list_foldr Primrec.id (.const (nilWord V)) hs) (fun _ => rfl)

def wordOfCode (n : ℕ) : ℕ := wordOfList V (Nat.natToList n)

theorem wordOfCode_primrec : Primrec (wordOfCode V) :=
  (wordOfList_primrec V).comp Primrec.nat_natToList

@[simp] theorem wordOfCode_nil : wordOfCode V 0=nilWord V := by simp [wordOfCode,Nat.natToList]
@[simp] theorem wordOfCode_adjoin (v rest : ℕ) :
    wordOfCode V (adjoin v rest)=consWord V v (wordOfCode V rest) := by
  simp only [wordOfCode,natToList_adjoin,wordOfList_cons]

theorem wordOfList_mem (L : List ℕ) (hL : ∀ v ∈ L,v ∈ V.support) :
    wordOfList V L ∈ (Syntax.Raw.uniformWords false (polynomial (⟨V⟩ : Total.TotalCategory P)) .unit).support := by
  induction L with
  | nil =>
      apply Syntax.Raw.uniformWords_constructor (polynomial (⟨V⟩ : Total.TotalCategory P)) .unit false
      simp [polynomial,Syntax.Raw.carrier,Syntax.Raw.taggedSum,Nat.unpair_pair,Total.terminalCarrier]
  | cons v L ih =>
      have hm := List.forall_mem_cons.mp hL
      apply Syntax.Raw.uniformWords_constructor (polynomial (⟨V⟩ : Total.TotalCategory P)) .unit false
      change ((Nat.unpair (Nat.pair (Nat.pair v (wordOfList V L)) 1)).2=0 ∧ _) ∨
        ((Nat.unpair (Nat.pair (Nat.pair v (wordOfList V L)) 1)).2=1 ∧ _)
      refine Or.inr ⟨by simp only [Nat.unpair_pair],?_⟩
      simp only [Nat.unpair_pair]
      change (Nat.unpair (Nat.pair v (wordOfList V L))).1 ∈ V.support ∧
        (Nat.unpair (Nat.pair v (wordOfList V L))).2 ∈
          (Syntax.Raw.uniformWords false (polynomial (⟨V⟩ : Total.TotalCategory P)) .unit).support
      simpa only [Nat.unpair_pair] using And.intro hm.1 (ih hm.2)

def wordMap : object V ⟶ Syntax.Raw.wordObject false (polynomial (⟨V⟩ : Total.TotalCategory P)) .unit :=
  ⟨Total.totalFromFunction (wordOfCode V) (wordOfCode_primrec V).to_comp
    (fun _ hn => wordOfList_mem V _ hn),Total.totalFromFunction_total _ _ _⟩

theorem wordMap_graph (n word : ℕ) :
    word ∈ Total.val (wordMap V).hom n ↔ n ∈ (carrier V).support ∧ word=wordOfCode V n :=
  Total.mem_totalFromFunction (X := carrier V)
    (Y := Syntax.Raw.uniformWords false (polynomial (⟨V⟩ : Total.TotalCategory P)) .unit)
    (wordOfCode V) (wordOfCode_primrec V).to_comp (fun _ hn => wordOfList_mem V _ hn) n word

theorem wordMap_nil (x : ℕ) (hx : x ∈ (Total.terminalCarrier (P := P)).support) :
    nilWord V ∈ Total.val ((nil V) ≫ wordMap V).hom x := by
  change nilWord V ∈ Total.val ((nil V).hom ≫ (wordMap V).hom) x
  rw [Total.val_comp]
  apply Part.mem_bind_iff.mpr
  exact ⟨0,(nil_graph V x 0).mpr ⟨hx,rfl⟩,(wordMap_graph V 0 (nilWord V)).mpr ⟨nil_mem V,(wordOfCode_nil V).symm⟩⟩

theorem wordMap_adjoin (v rest word : ℕ) :
    word ∈ Total.val ((adjoinMap V) ≫ wordMap V).hom (Nat.pair v rest) ↔
      v ∈ V.support ∧ rest ∈ (carrier V).support ∧ word=consWord V v (wordOfCode V rest) := by
  change word ∈ Total.val ((adjoinMap V).hom ≫ (wordMap V).hom) (Nat.pair v rest) ↔ _
  rw [Total.val_comp]
  simp only [Part.mem_bind_iff,adjoin_graph,wordMap_graph]
  constructor
  · rintro ⟨n,⟨hv,hr,rfl⟩,_,hw⟩
    exact ⟨hv,hr,by simpa only [wordOfCode_adjoin] using hw⟩
  · rintro ⟨hv,hr,hw⟩
    exact ⟨adjoin v rest,⟨hv,hr,rfl⟩,(adjoin_mem V v rest).mpr ⟨hv,hr⟩,
      by simpa only [wordOfCode_adjoin] using hw⟩

end CategoricalEssentialIncompleteness.V46.Miller.Lists
