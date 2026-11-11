/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerNamedSyntaxCharts
public import CategoricalEssentialIncompleteness.V46MillerSyntaxRawActionGraphs

/-! # Exact scalar graph of the actual polynomial input chart

Only the recursive-sort charts have scalar identity hypotheses. In the
application they are the constructed stored-word identity isomorphisms.
The polynomial comparison follows from its actual product and coproduct
triangles. Surjectivity of the chart and the existing unique-code theorem
give the reverse implication on every original word.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.Miller.NamedSyntaxComparison
open SyntacticSyntax
variable (P : Uniform.Family)
variable (X Y : PredicateCategory 𝗣𝗔) (X' Y' : Total.TotalCategory P)
variable (iX : X' ≅ (Syntax.predicateFunctor P).obj X)
  (iY : Y' ≅ (Syntax.predicateFunctor P).obj Y)

private theorem predicate_support {C : PredicateCategory 𝗣𝗔} (n : ℕ) :
    n∈((Syntax.predicateFunctor P).obj C).obj.support ↔ C.val.Evalb (M := ℕ) ![n] := by
  simp only [Syntax.predicateFunctor_object,Syntax.predicateObject_support,Set.mem_ofPred_eq]

private theorem functor_graph {C D : PredicateCategory 𝗣𝗔} (f : C ⟶ D)
    (x : PredicateInterpretation.Obj ℕ C) (y : PredicateInterpretation.Obj ℕ D) :
    y.val∈Total.val ((Syntax.predicateFunctor P).map f).hom x.val ↔
      (chosenGraph 𝗣𝗔 f).graph.val.Evalb (M := ℕ) ![x.val,y.val] := by
  rw [Syntax.predicateFunctor_graph]
  constructor
  · rintro ⟨a,ha,hb⟩
    have he : a=x := Subtype.ext ha
    subst a
    exact (chosenGraph_map_iff 𝗣𝗔 ℕ f x y).mpr (Subtype.ext hb)
  · intro h
    exact ⟨x,rfl,congrArg Subtype.val ((chosenGraph_map_iff 𝗣𝗔 ℕ f x y).mp h)⟩

private theorem inputIso_product (a b : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) :
    (inputIso P X Y X' Y' iX iY (.product a b)).hom =
      (Syntax.Raw.baseProductIso
        (Syntax.Raw.baseObject X' Y' (Syntax.Polynomial.mapped P a))
        (Syntax.Raw.baseObject X' Y' (Syntax.Polynomial.mapped P b))).hom ≫
      prod.map (inputIso P X Y X' Y' iX iY a).hom
        (inputIso P X Y X' Y' iX iY b).hom ≫
      inv (prodComparison (Syntax.predicateFunctor P) (a.eval.obj (X,Y)) (b.eval.obj (X,Y))) := by
  simp only [inputIso,Syntax.Polynomial.mapped,SyntaxPolynomial.mapCoefficients,
    Syntax.Raw.baseComparison,Syntax.Polynomial.component,SyntaxPolynomial.eval,
    SyntaxPolynomial.productFunctor,Functor.mapIso,Iso.trans_hom,Iso.trans_inv,
    Iso.symm_hom,asIso_inv,prod.mapIso_hom,prod.mapIso_inv,
    ← prod.map_map,Category.assoc]

private theorem inputIso_sum (a b : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) :
    (inputIso P X Y X' Y' iX iY (.sum a b)).hom =
      (Syntax.Raw.taggedSumIso
        (Syntax.Raw.baseObject X' Y' (Syntax.Polynomial.mapped P a))
        (Syntax.Raw.baseObject X' Y' (Syntax.Polynomial.mapped P b))).hom ≫
      (Syntax.Raw.baseCoproductIso
        (Syntax.Raw.baseObject X' Y' (Syntax.Polynomial.mapped P a))
        (Syntax.Raw.baseObject X' Y' (Syntax.Polynomial.mapped P b))).hom ≫
      coprod.map (inputIso P X Y X' Y' iX iY a).hom
        (inputIso P X Y X' Y' iX iY b).hom ≫
      coprodComparison (Syntax.predicateFunctor P) (a.eval.obj (X,Y)) (b.eval.obj (X,Y)) := by
  simp only [inputIso,Syntax.Polynomial.mapped,SyntaxPolynomial.mapCoefficients,
    Syntax.Raw.baseComparison,Syntax.Polynomial.component,SyntaxPolynomial.eval,
    SyntaxPolynomial.sumFunctor,Functor.mapIso,Iso.trans_hom,Iso.trans_inv,
    Iso.symm_hom,Iso.symm_inv,asIso_hom,coprod.mapIso_hom,coprod.mapIso_inv,
    ← coprod.map_map,Category.assoc]

@[reassoc] theorem inputIso_product_fst (a b : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) :
    (inputIso P X Y X' Y' iX iY (.product a b)).hom ≫
      (Syntax.predicateFunctor P).map (prod.fst : a.eval.obj (X,Y) ⨯ b.eval.obj (X,Y) ⟶ _) =
      Total.totalFst
        (Syntax.Raw.baseObject X' Y' (Syntax.Polynomial.mapped P a))
        (Syntax.Raw.baseObject X' Y' (Syntax.Polynomial.mapped P b)) ≫
      (inputIso P X Y X' Y' iX iY a).hom := by
  have hi : inv (prodComparison (Syntax.predicateFunctor P) (a.eval.obj (X,Y)) (b.eval.obj (X,Y))) ≫
      (Syntax.predicateFunctor P).map prod.fst = prod.fst := by
    rw [← prodComparison_fst]
    simp only [← Category.assoc,IsIso.inv_hom_id,Category.id_comp]
  rw [inputIso_product]
  erw [Category.assoc,Category.assoc,hi,prod.map_fst,← Category.assoc,Syntax.Raw.baseProductIso_fst]

@[reassoc] theorem inputIso_product_snd (a b : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) :
    (inputIso P X Y X' Y' iX iY (.product a b)).hom ≫
      (Syntax.predicateFunctor P).map (prod.snd : a.eval.obj (X,Y) ⨯ b.eval.obj (X,Y) ⟶ _) =
      Total.totalSnd
        (Syntax.Raw.baseObject X' Y' (Syntax.Polynomial.mapped P a))
        (Syntax.Raw.baseObject X' Y' (Syntax.Polynomial.mapped P b)) ≫
      (inputIso P X Y X' Y' iX iY b).hom := by
  have hi : inv (prodComparison (Syntax.predicateFunctor P) (a.eval.obj (X,Y)) (b.eval.obj (X,Y))) ≫
      (Syntax.predicateFunctor P).map prod.snd = prod.snd := by
    rw [← prodComparison_snd]
    simp only [← Category.assoc,IsIso.inv_hom_id,Category.id_comp]
  rw [inputIso_product]
  erw [Category.assoc,Category.assoc,hi,prod.map_snd,← Category.assoc,Syntax.Raw.baseProductIso_snd]

private theorem taggedInput_inl (A B : PredicateCategory 𝗣𝗔) (C D : Total.TotalCategory P)
    (f : C ⟶ (Syntax.predicateFunctor P).obj A) (g : D ⟶ (Syntax.predicateFunctor P).obj B) :
    Syntax.Raw.taggedInl C D ≫ ((Syntax.Raw.taggedSumIso C D).hom ≫
      (Syntax.Raw.baseCoproductIso C D).hom ≫ coprod.map f g ≫
        coprodComparison (Syntax.predicateFunctor P) A B) =
      f ≫ (Syntax.predicateFunctor P).map coprod.inl := by
  let u := Syntax.Raw.taggedInl C D
  let v := (Syntax.Raw.taggedSumIso C D).hom
  let w := (Syntax.Raw.baseCoproductIso C D).hom
  let k := coprod.map f g
  let t := coprodComparison (Syntax.predicateFunctor P) A B
  change u ≫ (v ≫ w ≫ k ≫ t) = f ≫ (Syntax.predicateFunctor P).map coprod.inl
  calc
    _ = ((u ≫ v) ≫ w) ≫ k ≫ t :=
      (Category.assoc u v (w ≫ k ≫ t)).symm.trans (Category.assoc (u ≫ v) w (k ≫ t)).symm
    _ = (Total.totalInl C D ≫ w) ≫ k ≫ t :=
      congrArg (fun z => (z ≫ w) ≫ k ≫ t) (Syntax.Raw.taggedInl_chart C D)
    _ = (coprod.inl : _ ⟶ C ⨿ D) ≫ k ≫ t :=
      congrArg (fun z => z ≫ k ≫ t) (Syntax.Raw.baseCoproductIso_inl C D)
    _ = f ≫ (coprod.inl ≫ t) :=
      (Category.assoc coprod.inl k t).symm.trans
        ((congrArg (fun z => z ≫ t) (coprod.inl_map f g)).trans (Category.assoc f coprod.inl t))
    _ = _ := congrArg (fun z => f ≫ z) (coprodComparison_inl (Syntax.predicateFunctor P))

private theorem taggedInput_inr (A B : PredicateCategory 𝗣𝗔) (C D : Total.TotalCategory P)
    (f : C ⟶ (Syntax.predicateFunctor P).obj A) (g : D ⟶ (Syntax.predicateFunctor P).obj B) :
    Syntax.Raw.taggedInr C D ≫ ((Syntax.Raw.taggedSumIso C D).hom ≫
      (Syntax.Raw.baseCoproductIso C D).hom ≫ coprod.map f g ≫
        coprodComparison (Syntax.predicateFunctor P) A B) =
      g ≫ (Syntax.predicateFunctor P).map coprod.inr := by
  let u := Syntax.Raw.taggedInr C D
  let v := (Syntax.Raw.taggedSumIso C D).hom
  let w := (Syntax.Raw.baseCoproductIso C D).hom
  let k := coprod.map f g
  let t := coprodComparison (Syntax.predicateFunctor P) A B
  change u ≫ (v ≫ w ≫ k ≫ t) = g ≫ (Syntax.predicateFunctor P).map coprod.inr
  calc
    _ = ((u ≫ v) ≫ w) ≫ k ≫ t :=
      (Category.assoc u v (w ≫ k ≫ t)).symm.trans (Category.assoc (u ≫ v) w (k ≫ t)).symm
    _ = (Total.totalInr C D ≫ w) ≫ k ≫ t :=
      congrArg (fun z => (z ≫ w) ≫ k ≫ t) (Syntax.Raw.taggedInr_chart C D)
    _ = (coprod.inr : _ ⟶ C ⨿ D) ≫ k ≫ t :=
      congrArg (fun z => z ≫ k ≫ t) (Syntax.Raw.baseCoproductIso_inr C D)
    _ = g ≫ (coprod.inr ≫ t) :=
      (Category.assoc coprod.inr k t).symm.trans
        ((congrArg (fun z => z ≫ t) (coprod.inr_map f g)).trans (Category.assoc g coprod.inr t))
    _ = _ := congrArg (fun z => g ≫ z) (coprodComparison_inr (Syntax.predicateFunctor P))

@[reassoc] theorem inputIso_sum_inl (a b : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) :
    Syntax.Raw.taggedInl
        (Syntax.Raw.baseObject X' Y' (Syntax.Polynomial.mapped P a))
        (Syntax.Raw.baseObject X' Y' (Syntax.Polynomial.mapped P b)) ≫
      (inputIso P X Y X' Y' iX iY (.sum a b)).hom =
      (inputIso P X Y X' Y' iX iY a).hom ≫
        (Syntax.predicateFunctor P).map coprod.inl := by
  rw [inputIso_sum]
  exact taggedInput_inl P _ _ _ _ _ _

@[reassoc] theorem inputIso_sum_inr (a b : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) :
    Syntax.Raw.taggedInr
        (Syntax.Raw.baseObject X' Y' (Syntax.Polynomial.mapped P a))
        (Syntax.Raw.baseObject X' Y' (Syntax.Polynomial.mapped P b)) ≫
      (inputIso P X Y X' Y' iX iY (.sum a b)).hom =
      (inputIso P X Y X' Y' iX iY b).hom ≫
        (Syntax.predicateFunctor P).map coprod.inr := by
  rw [inputIso_sum]
  exact taggedInput_inr P _ _ _ _ _ _

variable (hX : ∀ u v,v∈Total.val iX.hom.hom u ↔ u∈X'.obj.support ∧ v=u)
  (hY : ∀ u v,v∈Total.val iY.hom.hom u ↔ u∈Y'.obj.support ∧ v=u)

include hX hY in
theorem inputIso_forward (p : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) : ∀ u : ℕ,
    ∀ z : PredicateInterpretation.Obj ℕ (p.eval.obj (X,Y)),
    z.val∈Total.val (inputIso P X Y X' Y' iX iY p).hom.hom u →
      (baseRepresentation 𝗣𝗔 X Y p).val.Evalb (M := ℕ) ![u,z.val] := by
  induction p with
  | term =>
    intro u z h
    have h' : z.val∈Total.val iX.hom.hom u := by
      have he : (inputIso P X Y X' Y' iX iY .term).hom=iX.hom := by
        simp [inputIso,Syntax.Raw.baseComparison,Syntax.Polynomial.mapped,
          Syntax.Polynomial.component,SyntaxPolynomial.mapCoefficients,SyntaxPolynomial.eval]
        exact Category.id_comp _
      rwa [he] at h
    exact (baseRepresentation_term_eval 𝗣𝗔 ℕ X Y u z.val).mpr ⟨z.property,((hX u z.val).mp h').2⟩
  | formula =>
    intro u z h
    have h' : z.val∈Total.val iY.hom.hom u := by
      have he : (inputIso P X Y X' Y' iX iY .formula).hom=iY.hom := by
        simp [inputIso,Syntax.Raw.baseComparison,Syntax.Polynomial.mapped,
          Syntax.Polynomial.component,SyntaxPolynomial.mapCoefficients,SyntaxPolynomial.eval]
        exact Category.id_comp _
      rwa [he] at h
    exact (baseRepresentation_formula_eval 𝗣𝗔 ℕ X Y u z.val).mpr ⟨z.property,((hY u z.val).mp h').2⟩
  | coefficient C =>
    intro u z h
    have he : z.val=u := by
      have hi : (inputIso P X Y X' Y' iX iY (.coefficient C)).hom =
          𝟙 ((Syntax.predicateFunctor P).obj C) := by
        simp [inputIso,Syntax.Raw.baseComparison,Syntax.Polynomial.mapped,
          Syntax.Polynomial.component,SyntaxPolynomial.mapCoefficients,SyntaxPolynomial.eval]
      rw [hi] at h
      exact ((Total.mem_supportIdentity _ u z.val).mp h).2
    exact (baseRepresentation_coefficient_eval 𝗣𝗔 ℕ X Y C u z.val).mpr ⟨z.property,he⟩
  | unit =>
    intro u z h
    have hu : u=0 := Total.val_source (inputIso P X Y X' Y' iX iY .unit).hom.hom _ _ h
    exact (baseRepresentation_unit_eval 𝗣𝗔 ℕ X Y u z.val).mpr ⟨z.property,hu⟩
  | product a b ia ib =>
    intro u z h
    let x := (PredicateInterpretation.functor 𝗣𝗔 ℕ).map
      (prod.fst : a.eval.obj (X,Y) ⨯ b.eval.obj (X,Y) ⟶ _) z
    let y := (PredicateInterpretation.functor 𝗣𝗔 ℕ).map
      (prod.snd : a.eval.obj (X,Y) ⨯ b.eval.obj (X,Y) ⟶ _) z
    have hx := (Syntax.predicateFunctor_graph P prod.fst z.val x.val).mpr ⟨z,rfl,rfl⟩
    have hy := (Syntax.predicateFunctor_graph P prod.snd z.val y.val).mpr ⟨z,rfl,rfl⟩
    have hcx : x.val∈Total.val ((inputIso P X Y X' Y' iX iY (.product a b)).hom ≫
        (Syntax.predicateFunctor P).map prod.fst).hom u :=
      (Total.mem_val_comp _ _ _ _).mpr ⟨z.val,h,hx⟩
    have hcy : y.val∈Total.val ((inputIso P X Y X' Y' iX iY (.product a b)).hom ≫
        (Syntax.predicateFunctor P).map prod.snd).hom u :=
      (Total.mem_val_comp _ _ _ _).mpr ⟨z.val,h,hy⟩
    rw [inputIso_product_fst] at hcx
    rw [inputIso_product_snd] at hcy
    obtain ⟨v,hv,hva⟩ := (Total.mem_val_comp _ _ _ _).mp hcx
    obtain ⟨w,hw,hwb⟩ := (Total.mem_val_comp _ _ _ _).mp hcy
    obtain ⟨_,hv⟩ := (Total.mem_partialFst _ _ u v).mp hv
    obtain ⟨_,hw⟩ := (Total.mem_partialSnd _ _ u w).mp hw
    subst v
    subst w
    exact (baseRepresentation_product_eval 𝗣𝗔 ℕ X Y a b u z.val).mpr
      ⟨(Nat.unpair u).1,(Nat.unpair u).2,x.val,y.val,
        by simpa only [nat_pair_eq] using (Nat.pair_unpair u).symm,
        ia _ x hva,ib _ y hwb,(functor_graph P prod.fst z x).mp hx,
        (functor_graph P prod.snd z y).mp hy⟩
  | sum a b ia ib =>
    intro u z h
    have hu := Total.val_source (inputIso P X Y X' Y' iX iY (.sum a b)).hom.hom _ _ h
    rcases hu with ⟨ht,ha⟩ | ⟨ht,hb⟩
    · have hin : u∈Total.val (Syntax.Raw.taggedInl
        (Syntax.Raw.baseObject X' Y' (Syntax.Polynomial.mapped P a))
        (Syntax.Raw.baseObject X' Y' (Syntax.Polynomial.mapped P b))).hom (Nat.unpair u).1 := by
        apply (Total.mem_totalFromFunction _ _ (Syntax.Raw.taggedInl_supported
          (Syntax.Raw.baseObject X' Y' (Syntax.Polynomial.mapped P a))
          (Syntax.Raw.baseObject X' Y' (Syntax.Polynomial.mapped P b))) _ _).mpr
        exact ⟨ha,by simpa only [ht] using (Nat.pair_unpair u).symm⟩
      have hc : z.val∈Total.val (Syntax.Raw.taggedInl
          (Syntax.Raw.baseObject X' Y' (Syntax.Polynomial.mapped P a))
          (Syntax.Raw.baseObject X' Y' (Syntax.Polynomial.mapped P b)) ≫
          (inputIso P X Y X' Y' iX iY (.sum a b)).hom).hom (Nat.unpair u).1 :=
        (Total.mem_val_comp _ _ _ _).mpr ⟨u,hin,h⟩
      rw [inputIso_sum_inl] at hc
      obtain ⟨v,hv,hvz⟩ := (Total.mem_val_comp _ _ _ _).mp hc
      let x : PredicateInterpretation.Obj ℕ (a.eval.obj (X,Y)) :=
        ⟨v,(predicate_support P v).mp (Total.val_target _ _ _ hv)⟩
      exact (baseRepresentation_sum_eval 𝗣𝗔 ℕ X Y a b u z.val).mpr
        (Or.inl ⟨(Nat.unpair u).1,v,
          by simpa only [nat_pair_eq,ht] using (Nat.pair_unpair u).symm,
          ia _ x hv,(functor_graph P coprod.inl x z).mp hvz⟩)
    · have hin : u∈Total.val (Syntax.Raw.taggedInr
        (Syntax.Raw.baseObject X' Y' (Syntax.Polynomial.mapped P a))
        (Syntax.Raw.baseObject X' Y' (Syntax.Polynomial.mapped P b))).hom (Nat.unpair u).1 := by
        apply (Total.mem_totalFromFunction _ _ (Syntax.Raw.taggedInr_supported
          (Syntax.Raw.baseObject X' Y' (Syntax.Polynomial.mapped P a))
          (Syntax.Raw.baseObject X' Y' (Syntax.Polynomial.mapped P b))) _ _).mpr
        exact ⟨hb,by simpa only [ht] using (Nat.pair_unpair u).symm⟩
      have hc : z.val∈Total.val (Syntax.Raw.taggedInr
          (Syntax.Raw.baseObject X' Y' (Syntax.Polynomial.mapped P a))
          (Syntax.Raw.baseObject X' Y' (Syntax.Polynomial.mapped P b)) ≫
          (inputIso P X Y X' Y' iX iY (.sum a b)).hom).hom (Nat.unpair u).1 :=
        (Total.mem_val_comp _ _ _ _).mpr ⟨u,hin,h⟩
      rw [inputIso_sum_inr] at hc
      obtain ⟨v,hv,hvz⟩ := (Total.mem_val_comp _ _ _ _).mp hc
      let x : PredicateInterpretation.Obj ℕ (b.eval.obj (X,Y)) :=
        ⟨v,(predicate_support P v).mp (Total.val_target _ _ _ hv)⟩
      exact (baseRepresentation_sum_eval 𝗣𝗔 ℕ X Y a b u z.val).mpr
        (Or.inr ⟨(Nat.unpair u).1,v,
          by simpa only [nat_pair_eq,ht] using (Nat.pair_unpair u).symm,
          ib _ x hv,(functor_graph P coprod.inr x z).mp hvz⟩)

include hX hY in
theorem inputIso_graph (p : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) (u : ℕ)
    (z : PredicateInterpretation.Obj ℕ (p.eval.obj (X,Y))) :
    z.val∈Total.val (inputIso P X Y X' Y' iX iY p).hom.hom u ↔
      (baseRepresentation 𝗣𝗔 X Y p).val.Evalb (M := ℕ) ![u,z.val] := by
  constructor
  · exact inputIso_forward P X Y X' Y' iX iY hX hY p u z
  · intro h
    let e := inputIso P X Y X' Y' iX iY p
    have hz : z.val∈((Syntax.predicateFunctor P).obj (p.eval.obj (X,Y))).obj.support :=
      (predicate_support P z.val).mpr z.property
    obtain ⟨v,hv⟩ := Part.dom_iff_mem.mp ((Total.total_iff e.inv.hom).mp e.inv.property z.val hz)
    have hv' : z.val∈Total.val e.hom.hom v := (Syntax.Raw.totalIso_graph_symm e v z.val).mpr hv
    have hr := inputIso_forward P X Y X' Y' iX iY hX hY p v z hv'
    have he := baseRepresentation_code_unique 𝗣𝗔 ℕ X Y p u v z.val h hr
    subst v
    exact hv'

end CategoricalEssentialIncompleteness.V46.Miller.NamedSyntaxComparison
