/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerSyntaxRaw
public import CategoricalEssentialIncompleteness.V46MillerTotalFiniteCoproducts

/-! # Literal polynomial carriers and their chosen categorical values

The comparison preserves the actual ordered product projections and tagged
sum constructors. Every coefficient is an arbitrary uniform semidecidable
carrier. The sum chart translates Nat.pair(value,tag) into 2*value+tag
and proves the inverse translation on the appropriate carrier supports.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw

variable {P : Uniform.Family}

def baseObject (A B : Total.TotalCategory P) (p : SyntaxPolynomial (Total.TotalCategory P)) : Total.TotalCategory P :=
  ⟨carrier A.obj B.obj p⟩

def baseUnitIso : (⟨Total.terminalCarrier⟩ : Total.TotalCategory P) ≅ ⊤_ (Total.TotalCategory P) :=
  (Total.terminalIsTerminal (P := P)).uniqueUpToIso (Limits.terminalIsTerminal (C := Total.TotalCategory P))

theorem baseUnitIso_inverse_value (n : ℕ) (hn : n∈(⊤_ (Total.TotalCategory P)).obj.support) :
    Total.val (baseUnitIso (P := P)).inv.hom n=Part.some 0 := by
  obtain ⟨m,hm⟩ := Part.dom_iff_mem.mp
    ((Total.total_iff (baseUnitIso (P := P)).inv.hom).mp (baseUnitIso (P := P)).inv.property n hn)
  have hm0 : m=0 := Total.val_target (baseUnitIso (P := P)).inv.hom n m hm
  exact Part.eq_some_iff.mpr (hm0 ▸ hm)

def baseProductIso (C D : Total.TotalCategory P) :
    (⟨Total.product C.obj D.obj⟩ : Total.TotalCategory P) ≅ C ⨯ D :=
  (Total.productIsLimit C D).conePointUniqueUpToIso (limit.isLimit (Limits.pair C D))

@[simp, reassoc] theorem baseProductIso_fst (C D : Total.TotalCategory P) :
    (baseProductIso C D).hom ≫ prod.fst=Total.totalFst C D :=
  IsLimit.conePointUniqueUpToIso_hom_comp (Total.productIsLimit C D) (limit.isLimit (Limits.pair C D)) ⟨.left⟩

@[simp, reassoc] theorem baseProductIso_snd (C D : Total.TotalCategory P) :
    (baseProductIso C D).hom ≫ prod.snd=Total.totalSnd C D :=
  IsLimit.conePointUniqueUpToIso_hom_comp (Total.productIsLimit C D) (limit.isLimit (Limits.pair C D)) ⟨.right⟩

@[simp, reassoc] theorem baseProductIso_inv_fst (C D : Total.TotalCategory P) :
    (baseProductIso C D).inv ≫ Total.totalFst C D=prod.fst :=
  IsLimit.conePointUniqueUpToIso_inv_comp (Total.productIsLimit C D) (limit.isLimit (Limits.pair C D)) ⟨.left⟩

@[simp, reassoc] theorem baseProductIso_inv_snd (C D : Total.TotalCategory P) :
    (baseProductIso C D).inv ≫ Total.totalSnd C D=prod.snd :=
  IsLimit.conePointUniqueUpToIso_inv_comp (Total.productIsLimit C D) (limit.isLimit (Limits.pair C D)) ⟨.right⟩

def baseCoproductIso (C D : Total.TotalCategory P) : Total.totalCoproduct C D ≅ C ⨿ D :=
  (Total.coproductIsColimit C D).coconePointUniqueUpToIso (colimit.isColimit (Limits.pair C D))

@[simp, reassoc] theorem baseCoproductIso_inl (C D : Total.TotalCategory P) :
    Total.totalInl C D ≫ (baseCoproductIso C D).hom=coprod.inl :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (Total.coproductIsColimit C D) (colimit.isColimit (Limits.pair C D)) ⟨.left⟩

@[simp, reassoc] theorem baseCoproductIso_inr (C D : Total.TotalCategory P) :
    Total.totalInr C D ≫ (baseCoproductIso C D).hom=coprod.inr :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (Total.coproductIsColimit C D) (colimit.isColimit (Limits.pair C D)) ⟨.right⟩

@[simp, reassoc] theorem baseCoproductIso_inv_inl (C D : Total.TotalCategory P) :
    coprod.inl ≫ (baseCoproductIso C D).inv=Total.totalInl C D :=
  IsColimit.comp_coconePointUniqueUpToIso_inv
    (Total.coproductIsColimit C D) (colimit.isColimit (Limits.pair C D)) ⟨.left⟩

@[simp, reassoc] theorem baseCoproductIso_inv_inr (C D : Total.TotalCategory P) :
    coprod.inr ≫ (baseCoproductIso C D).inv=Total.totalInr C D :=
  IsColimit.comp_coconePointUniqueUpToIso_inv
    (Total.coproductIsColimit C D) (colimit.isColimit (Limits.pair C D)) ⟨.right⟩

def taggedSumObject (C D : Total.TotalCategory P) : Total.TotalCategory P := ⟨taggedSum C.obj D.obj⟩

def tagToParity (n : ℕ) : ℕ := 2*(Nat.unpair n).1+(Nat.unpair n).2
def parityToTag (n : ℕ) : ℕ := Nat.pair (n/2) (n%2)

theorem tagToParity_computable : Computable tagToParity :=
  Primrec.nat_add.to_comp.comp
    (Primrec.nat_mul.to_comp.comp (Computable.const 2) (Computable.fst.comp Computable.unpair))
    (Computable.snd.comp Computable.unpair)

theorem parityToTag_computable : Computable parityToTag :=
  Primrec₂.natPair.to_comp.comp
    (Primrec.nat_div.to_comp.comp Computable.id (Computable.const 2))
    (Primrec.nat_mod.to_comp.comp Computable.id (Computable.const 2))

theorem tagToParity_supported (C D : Total.TotalCategory P) (n : ℕ)
    (hn : n ∈ (taggedSum C.obj D.obj).support) :
    tagToParity n ∈ (Total.coproduct C.obj D.obj).support := by
  obtain ⟨ht,hC⟩ | ⟨ht,hD⟩ := hn
  · simpa only [tagToParity,ht,Nat.add_zero] using
      (Total.mem_coproduct_even C.obj D.obj (Nat.unpair n).1).mpr hC
  · simpa only [tagToParity,ht] using
      (Total.mem_coproduct_odd C.obj D.obj (Nat.unpair n).1).mpr hD

theorem parityToTag_supported (C D : Total.TotalCategory P) (n : ℕ)
    (hn : n ∈ (Total.coproduct C.obj D.obj).support) :
    parityToTag n ∈ (taggedSum C.obj D.obj).support := by
  change (((Nat.unpair (parityToTag n)).2=0 ∧ (Nat.unpair (parityToTag n)).1∈C.obj.support) ∨
    ((Nat.unpair (parityToTag n)).2=1 ∧ (Nat.unpair (parityToTag n)).1∈D.obj.support))
  change (n%2=0 ∧ n/2∈C.obj.support) ∨ (n%2=1 ∧ n/2∈D.obj.support) at hn
  simpa only [parityToTag,Nat.unpair_pair] using hn

theorem parityToTag_tagToParity (C D : Total.TotalCategory P) (n : ℕ)
    (hn : n ∈ (taggedSum C.obj D.obj).support) : parityToTag (tagToParity n)=n := by
  have he : parityToTag (tagToParity n)=Nat.pair (Nat.unpair n).1 (Nat.unpair n).2 := by
    obtain ⟨ht,_⟩ | ⟨ht,_⟩ := hn
    · simp [tagToParity,parityToTag,ht]
    · simp [tagToParity,parityToTag,ht,Nat.add_div,Nat.add_mod]
  exact he.trans (Nat.pair_unpair n)

theorem tagToParity_parityToTag (n : ℕ) : tagToParity (parityToTag n)=n := by
  simp only [tagToParity,parityToTag,Nat.unpair_pair]
  omega

private theorem fromFunction_at {C D : Total.Carrier P} (f : ℕ → ℕ) (hf : Computable f)
    (hs : ∀ n,n∈C.support → f n∈D.support) (n : ℕ) (hn : n∈C.support) :
    Total.val (Total.totalFromFunction f hf hs) n=Part.some (f n) :=
  Part.eq_some_iff.mpr ((Total.mem_totalFromFunction f hf hs n (f n)).mpr ⟨hn,rfl⟩)

def taggedSumIso (C D : Total.TotalCategory P) : taggedSumObject C D ≅ Total.totalCoproduct C D where
  hom := ⟨Total.totalFromFunction tagToParity tagToParity_computable (tagToParity_supported C D),
    Total.totalFromFunction_total _ _ _⟩
  inv := ⟨Total.totalFromFunction parityToTag parityToTag_computable (parityToTag_supported C D),
    Total.totalFromFunction_total _ _ _⟩
  hom_inv_id := by
    apply WideSubcategory.hom_ext
    apply Total.val_ext_on_source
    intro n hn
    change Total.val ((Total.totalFromFunction tagToParity tagToParity_computable (tagToParity_supported C D)) ≫ (Total.totalFromFunction parityToTag parityToTag_computable (parityToTag_supported C D))) n=
      Total.supportIdentity (taggedSum C.obj D.obj).support n
    rw [Total.val_comp,fromFunction_at tagToParity tagToParity_computable (tagToParity_supported C D) n hn,Part.bind_some,
      fromFunction_at parityToTag parityToTag_computable (parityToTag_supported C D) _
        (tagToParity_supported C D n hn),parityToTag_tagToParity C D n hn]
    exact (Part.eq_some_iff.mpr ((Total.mem_supportIdentity _ n n).mpr ⟨hn,rfl⟩)).symm
  inv_hom_id := by
    apply WideSubcategory.hom_ext
    apply Total.val_ext_on_source
    intro n hn
    change Total.val ((Total.totalFromFunction parityToTag parityToTag_computable (parityToTag_supported C D)) ≫ (Total.totalFromFunction tagToParity tagToParity_computable (tagToParity_supported C D))) n=
      Total.supportIdentity (Total.coproduct C.obj D.obj).support n
    rw [Total.val_comp,fromFunction_at parityToTag parityToTag_computable (parityToTag_supported C D) n hn,Part.bind_some,
      fromFunction_at tagToParity tagToParity_computable (tagToParity_supported C D) _
        (parityToTag_supported C D n hn),tagToParity_parityToTag]
    exact (Part.eq_some_iff.mpr ((Total.mem_supportIdentity _ n n).mpr ⟨hn,rfl⟩)).symm

theorem taggedSumIso_hom_graph (C D : Total.TotalCategory P) (n m : ℕ) :
    m ∈ Total.val (taggedSumIso C D).hom.hom n ↔
      n∈(taggedSum C.obj D.obj).support ∧ m=2*(Nat.unpair n).1+(Nat.unpair n).2 :=
  Total.mem_totalFromFunction tagToParity tagToParity_computable (tagToParity_supported C D) n m

theorem taggedSumIso_inv_graph (C D : Total.TotalCategory P) (n m : ℕ) :
    m ∈ Total.val (taggedSumIso C D).inv.hom n ↔
      n∈(Total.coproduct C.obj D.obj).support ∧ m=Nat.pair (n/2) (n%2) :=
  Total.mem_totalFromFunction parityToTag parityToTag_computable (parityToTag_supported C D) n m

theorem taggedInl_supported (C D:Total.TotalCategory P) (n:ℕ) (hn:n∈C.obj.support) :
    Nat.pair n 0∈(taggedSum C.obj D.obj).support := by
  change ((Nat.unpair (Nat.pair n 0)).2=0 ∧ (Nat.unpair (Nat.pair n 0)).1∈C.obj.support) ∨
    ((Nat.unpair (Nat.pair n 0)).2=1 ∧ (Nat.unpair (Nat.pair n 0)).1∈D.obj.support)
  rw [Nat.unpair_pair]
  exact Or.inl ⟨rfl,hn⟩

theorem taggedInr_supported (C D:Total.TotalCategory P) (n:ℕ) (hn:n∈D.obj.support) :
    Nat.pair n 1∈(taggedSum C.obj D.obj).support := by
  change ((Nat.unpair (Nat.pair n 1)).2=0 ∧ (Nat.unpair (Nat.pair n 1)).1∈C.obj.support) ∨
    ((Nat.unpair (Nat.pair n 1)).2=1 ∧ (Nat.unpair (Nat.pair n 1)).1∈D.obj.support)
  rw [Nat.unpair_pair]
  exact Or.inr ⟨rfl,hn⟩

def taggedInl (C D : Total.TotalCategory P) : C ⟶ taggedSumObject C D :=
  ⟨Total.totalFromFunction (fun n => Nat.pair n 0)
    (Primrec₂.natPair.to_comp.comp Computable.id (Computable.const 0))
    (taggedInl_supported C D),
      Total.totalFromFunction_total _ _ _⟩

def taggedInr (C D : Total.TotalCategory P) : D ⟶ taggedSumObject C D :=
  ⟨Total.totalFromFunction (fun n => Nat.pair n 1)
    (Primrec₂.natPair.to_comp.comp Computable.id (Computable.const 1))
    (taggedInr_supported C D),
      Total.totalFromFunction_total _ _ _⟩

@[simp, reassoc] theorem taggedInl_chart (C D : Total.TotalCategory P) :
    taggedInl C D ≫ (taggedSumIso C D).hom=Total.totalInl C D := by
  apply WideSubcategory.hom_ext
  apply Total.val_ext_on_source
  intro n hn
  have hs := taggedInl_supported C D n hn
  change Total.val ((Total.totalFromFunction (fun n => Nat.pair n 0)
    (Primrec₂.natPair.to_comp.comp Computable.id (Computable.const 0))
    (taggedInl_supported C D)) ≫ (Total.totalFromFunction tagToParity tagToParity_computable
      (tagToParity_supported C D))) n = Total.val (Total.inl C.obj D.obj) n
  rw [Total.val_comp,fromFunction_at (fun n => Nat.pair n 0)
    (Primrec₂.natPair.to_comp.comp Computable.id (Computable.const 0))
    (taggedInl_supported C D) n hn,Part.bind_some,
    fromFunction_at tagToParity tagToParity_computable (tagToParity_supported C D) _ hs]
  simpa only [tagToParity,Nat.unpair_pair,Nat.add_zero] using (Total.val_inl_at C.obj D.obj n hn).symm

@[simp, reassoc] theorem taggedInr_chart (C D : Total.TotalCategory P) :
    taggedInr C D ≫ (taggedSumIso C D).hom=Total.totalInr C D := by
  apply WideSubcategory.hom_ext
  apply Total.val_ext_on_source
  intro n hn
  have hs := taggedInr_supported C D n hn
  change Total.val ((Total.totalFromFunction (fun n => Nat.pair n 1)
    (Primrec₂.natPair.to_comp.comp Computable.id (Computable.const 1))
    (taggedInr_supported C D)) ≫ (Total.totalFromFunction tagToParity tagToParity_computable
      (tagToParity_supported C D))) n = Total.val (Total.inr C.obj D.obj) n
  rw [Total.val_comp,fromFunction_at (fun n => Nat.pair n 1)
    (Primrec₂.natPair.to_comp.comp Computable.id (Computable.const 1))
    (taggedInr_supported C D) n hn,Part.bind_some,
    fromFunction_at tagToParity tagToParity_computable (tagToParity_supported C D) _ hs]
  simpa only [tagToParity,Nat.unpair_pair] using (Total.val_inr_at C.obj D.obj n hn).symm

@[simp, reassoc] theorem taggedInl_chart_inv (C D : Total.TotalCategory P) :
    Total.totalInl C D ≫ (taggedSumIso C D).inv=taggedInl C D := by
  have h := congrArg (fun f => f ≫ (taggedSumIso C D).inv) (taggedInl_chart C D)
  simpa only [Category.assoc,Iso.hom_inv_id,Category.comp_id] using h.symm

@[simp, reassoc] theorem taggedInr_chart_inv (C D : Total.TotalCategory P) :
    Total.totalInr C D ≫ (taggedSumIso C D).inv=taggedInr C D := by
  have h := congrArg (fun f => f ≫ (taggedSumIso C D).inv) (taggedInr_chart C D)
  simpa only [Category.assoc,Iso.hom_inv_id,Category.comp_id] using h.symm

/-- Every raw coefficient and every sort is compared without changing
its carrier. Only the literal finite product/sum presentations are charted. -/
def baseComparison (A B : Total.TotalCategory P) : (p : SyntaxPolynomial (Total.TotalCategory P)) →
    (⟨carrier A.obj B.obj p⟩ : Total.TotalCategory P) ≅ p.eval.obj (A,B)
  | .term => Iso.refl A
  | .formula => Iso.refl B
  | .coefficient C => Iso.refl C
  | .unit => baseUnitIso
  | .product a b =>
      baseProductIso (baseObject A B a) (baseObject A B b) ≪≫
        prod.mapIso (baseComparison A B a) (baseComparison A B b)
  | .sum a b =>
      taggedSumIso (baseObject A B a) (baseObject A B b) ≪≫
        baseCoproductIso (baseObject A B a) (baseObject A B b) ≪≫
          coprod.mapIso (baseComparison A B a) (baseComparison A B b)

@[simp, reassoc] theorem baseComparison_product_fst (A B : Total.TotalCategory P)
    (a b : SyntaxPolynomial (Total.TotalCategory P)) :
    (baseComparison A B (.product a b)).hom ≫ prod.fst=
      Total.totalFst (baseObject A B a) (baseObject A B b) ≫ (baseComparison A B a).hom := by
  simp only [baseComparison,Iso.trans_hom,prod.mapIso_hom,Category.assoc,
    prod.map_fst,baseProductIso_fst_assoc]

@[simp, reassoc] theorem baseComparison_product_snd (A B : Total.TotalCategory P)
    (a b : SyntaxPolynomial (Total.TotalCategory P)) :
    (baseComparison A B (.product a b)).hom ≫ prod.snd=
      Total.totalSnd (baseObject A B a) (baseObject A B b) ≫ (baseComparison A B b).hom := by
  simp only [baseComparison,Iso.trans_hom,prod.mapIso_hom,Category.assoc,
    prod.map_snd,baseProductIso_snd_assoc]

@[simp, reassoc] theorem baseComparison_sum_inl (A B : Total.TotalCategory P)
    (a b : SyntaxPolynomial (Total.TotalCategory P)) :
    taggedInl (baseObject A B a) (baseObject A B b) ≫ (baseComparison A B (.sum a b)).hom=
      (baseComparison A B a).hom ≫ coprod.inl := by
  simp only [baseComparison,Iso.trans_hom,coprod.mapIso_hom,← Category.assoc,
    taggedInl_chart,baseCoproductIso_inl,coprod.inl_map]

@[simp, reassoc] theorem baseComparison_sum_inr (A B : Total.TotalCategory P)
    (a b : SyntaxPolynomial (Total.TotalCategory P)) :
    taggedInr (baseObject A B a) (baseObject A B b) ≫ (baseComparison A B (.sum a b)).hom=
      (baseComparison A B b).hom ≫ coprod.inr := by
  simp only [baseComparison,Iso.trans_hom,coprod.mapIso_hom,← Category.assoc,
    taggedInr_chart,baseCoproductIso_inr,coprod.inr_map]

@[simp, reassoc] theorem baseComparison_product_inv_fst (A B : Total.TotalCategory P)
    (a b : SyntaxPolynomial (Total.TotalCategory P)) :
    (baseComparison A B (.product a b)).inv ≫ Total.totalFst (baseObject A B a) (baseObject A B b)=
      prod.fst ≫ (baseComparison A B a).inv := by
  simp only [baseComparison,Iso.trans_inv,prod.mapIso_inv,Category.assoc,
    baseProductIso_inv_fst,prod.map_fst]

@[simp, reassoc] theorem baseComparison_product_inv_snd (A B : Total.TotalCategory P)
    (a b : SyntaxPolynomial (Total.TotalCategory P)) :
    (baseComparison A B (.product a b)).inv ≫ Total.totalSnd (baseObject A B a) (baseObject A B b)=
      prod.snd ≫ (baseComparison A B b).inv := by
  simp only [baseComparison,Iso.trans_inv,prod.mapIso_inv,Category.assoc,
    baseProductIso_inv_snd,prod.map_snd]

@[simp, reassoc] theorem baseComparison_sum_inv_inl (A B : Total.TotalCategory P)
    (a b : SyntaxPolynomial (Total.TotalCategory P)) :
    coprod.inl ≫ (baseComparison A B (.sum a b)).inv=
      (baseComparison A B a).inv ≫ taggedInl (baseObject A B a) (baseObject A B b) := by
  apply (cancel_mono (baseComparison A B (.sum a b)).hom).mp
  rw [Category.assoc,Iso.inv_hom_id,Category.comp_id,
    Category.assoc,baseComparison_sum_inl,← Category.assoc,Iso.inv_hom_id,Category.id_comp]

@[simp, reassoc] theorem baseComparison_sum_inv_inr (A B : Total.TotalCategory P)
    (a b : SyntaxPolynomial (Total.TotalCategory P)) :
    coprod.inr ≫ (baseComparison A B (.sum a b)).inv=
      (baseComparison A B b).inv ≫ taggedInr (baseObject A B a) (baseObject A B b) := by
  apply (cancel_mono (baseComparison A B (.sum a b)).hom).mp
  rw [Category.assoc,Iso.inv_hom_id,Category.comp_id,
    Category.assoc,baseComparison_sum_inr,← Category.assoc,Iso.inv_hom_id,Category.id_comp]

theorem baseComparison_coefficient_graph (A B C : Total.TotalCategory P) (n m : ℕ) :
    m ∈ Total.val (baseComparison A B (.coefficient C)).inv.hom n ↔ n∈C.obj.support ∧ m=n :=
  Total.mem_supportIdentity C.obj.support n m

end CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
