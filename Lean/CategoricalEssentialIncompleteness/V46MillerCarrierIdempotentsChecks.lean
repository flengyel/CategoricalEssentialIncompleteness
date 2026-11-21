/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerCarrierIdempotents


/-! # Restriction idempotents on uniformly semidecidable carriers -/

@[expose] public section
open CategoryTheory CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.CarrierIdempotents
attribute [instance 2000] Uniform.nativeRestriction
variable {P : Uniform.Family}

example (A : Total.Carrier P) : Idem (Total.inclusion.obj A) ≃o
    {B : Set ℕ // Uniform.Enumerable P (·∈B) ∧ B⊆A.support} := supportOrderIso A

example (A : Total.Carrier P) (B : Set ℕ) (hB : Uniform.Enumerable P (·∈B)) (hBA : B⊆A.support) :
    ∃! c : Idem (Total.inclusion.obj A),support c=B := exists_unique_support A B hB hBA

example (A : Total.Carrier P) : support (⊤ : Idem (Total.inclusion.obj A))=A.support := support_top A
example (A : Total.Carrier P) : support (⊥ : Idem (Total.inclusion.obj A))=∅ := support_bot A

example {A : Total.Carrier P} (c : Idem (Total.inclusion.obj A)) :
    c.hom.hom.val=Total.supportIdentity (support c) := value_idem c

example {A : Total.Carrier P} (c d : Idem (Total.inclusion.obj A)) :
    c⊔d≠⊤ ↔ support c∪support d≠A.support := join_ne_top_iff c d
example {A : Total.Carrier P} (c d : Idem (Total.inclusion.obj A)) :
    Complementary c d ↔ Disjoint (support c) (support d) ∧ support c∪support d=A.support :=
  complementary_iff c d

example {A B : Total.Carrier P} (f : A ⟶ B) (c : Idem (Total.inclusion.obj B)) :
    support (Idem.pull (Total.inclusion.map f) c)={x | ∃ y,y∈Total.val f x ∧ y∈support c} :=
  support_pull f c

example {A B : Total.TotalCategory P} (f : A ⟶ B) (c : Idem (Total.inclusion.obj B.obj))
    (x : {n // n∈A.obj.support}) :
    x.val∈support (Idem.pull (Total.inclusion.map f.hom) c) ↔
      (Total.totalFunction f x).val∈support c := support_pull_total f c x

example {A B : Total.Carrier P} (f : A ⟶ B) (L : List (Idem (Total.inclusion.obj B))) :
    Idem.pull (Total.inclusion.map f) (finiteSup L)=
      finiteSup (L.map (Idem.pull (Total.inclusion.map f))) := pull_finiteSup f L

example {A B : Total.Carrier P} (f : A ⟶ B) :
    support (Ranges.range (Total.inclusion.map f))={y | ∃ x,y∈Total.val f x} := support_range f

example {A B : Total.TotalCategory P} (f : A ⟶ B) : (Total.imageObject f).obj.support=
    Set.range (fun x : {n // n∈A.obj.support} => (Total.totalFunction f x).val) :=
  (imageObject_support f).trans (range_totalFunction f)

example (p : Bits) (B : Set ℕ) :
    Uniform.Enumerable (Uniform.Family.singleton p) (·∈B) ↔
      Nat.RecursiveIn (OracleComputation.oracleSet (OracleRelative.oracleSupport p))
        (Total.supportIdentity B) := singleton_enumerable_iff_recursive_identity p B

example (p : Bits) (A : Total.Carrier (Uniform.Family.singleton p)) (B : Set ℕ) :
    (∃ c : Idem (Total.inclusion.obj A),support c=B) ↔
      B⊆A.support ∧ Nat.RecursiveIn (OracleComputation.oracleSet (OracleRelative.oracleSupport p))
        (Total.supportIdentity B) := singleton_exists_support_iff p A B

end CategoricalEssentialIncompleteness.V46.Miller.CarrierIdempotents
