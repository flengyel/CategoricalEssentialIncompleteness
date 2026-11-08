/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46MillerNamedSyntaxComparison
import CategoricalEssentialIncompleteness.V46MillerListsStable
import CategoricalEssentialIncompleteness.V46SyntacticLists
import CategoricalEssentialIncompleteness.V46NumericalPolynomialRepresentation

/-! # The actual list comparison for a PA-described coefficient predicate

The scalar list code is unchanged in both directions. Nil and ordered
adjoin are compared as morphisms, then their algebra isomorphism transports
the already constructed arbitrary-target universal property.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
namespace CategoricalEssentialIncompleteness.V46.Miller.NamedSyntaxComparison
variable (P : Uniform.Family) (C : PredicateCategory 𝗣𝗔)
local notation "F" => Syntax.predicateFunctor P
local notation "L₀" => SyntacticLists.algebra 𝗣𝗔 C
private abbrev directListAlgebra (P : Uniform.Family) (C : PredicateCategory 𝗣𝗔) :
    ListAlgebra ((Syntax.predicateFunctor P).obj C) := Lists.algebra ((Syntax.predicateFunctor P).obj C).obj
local notation "L₁" => directListAlgebra P C

theorem list_support (word : ℕ) :
    word∈(Lists.carrier ((F).obj C).obj).support ↔
      (SyntacticLists.listObject 𝗣𝗔 C).val.Evalb (M := ℕ) ![word] := by
  change word∈(Lists.carrier ((F).obj C).obj).support ↔
    (SyntacticLists.listCarrier C).val.Evalb (M := ℕ) ![word]
  rw [SyntacticLists.listCarrier_eval]
  change (∀ entry∈Nat.natToList word,entry∈((F).obj C).obj.support) ↔ _
  simp only [Syntax.Raw.mapped_coefficient_support,List.forall_mem_iff_getElem]
  constructor
  · intro h i hi
    have hi' : i<(Nat.natToList word).length := by simpa only [NatVectors.len_eq_decode] using hi
    simpa only [NatVectors.nth_eq_decode,List.getD_eq_getElem (Nat.natToList word) 0 hi'] using h i hi'
  · intro h i hi
    have hi' : i<len word := by simpa only [NatVectors.len_eq_decode] using hi
    simpa only [NatVectors.nth_eq_decode,List.getD_eq_getElem (Nat.natToList word) 0 hi] using h i hi'

def listIso : Lists.object ((F).obj C).obj ≅ (F).obj (SyntacticLists.listObject 𝗣𝗔 C) :=
  identityIso P _ _ (fun word => (list_support P C word).trans
    (Syntax.Raw.mapped_coefficient_support (P := P) (SyntacticLists.listObject 𝗣𝗔 C) word).symm)

theorem listIso_graph (word output : ℕ) :
    output∈Total.val (listIso P C).hom.hom word ↔
      word∈(Lists.carrier ((F).obj C).obj).support ∧ output=word :=
  identityIso_graph P _ _ (fun word => (list_support P C word).trans
    (Syntax.Raw.mapped_coefficient_support (P := P) (SyntacticLists.listObject 𝗣𝗔 C) word).symm) word output

theorem listIso_inverse_graph (word output : ℕ) :
    output∈Total.val (listIso P C).inv.hom word ↔
      word∈((F).obj (SyntacticLists.listObject 𝗣𝗔 C)).obj.support ∧ output=word :=
  identityIso_inverse_graph P _ _ (fun word => (list_support P C word).trans
    (Syntax.Raw.mapped_coefficient_support (P := P) (SyntacticLists.listObject 𝗣𝗔 C) word).symm) word output

def mappedListAlgebra : ListAlgebra ((F).obj C) where
  carrier := (F).obj (L₀).carrier
  nil := inv (terminalComparison (F)) ≫ (F).map (L₀).nil
  cons := inv (prodComparison (F) C (L₀).carrier) ≫ (F).map (L₀).cons

private theorem raw_nil_comparison :
    (inputIso P (L₀).carrier (L₀).carrier (L₁).carrier (L₁).carrier (listIso P C) (listIso P C) .unit).hom ≫
      (F).map (L₀).nil=Lists.nil ((F).obj C).obj ≫ (listIso P C).hom := by
  apply operation_square P (L₀).carrier (L₀).carrier (L₀).carrier
    (L₁).carrier (L₁).carrier (L₁).carrier (listIso P C) (listIso P C) (listIso P C)
    (listIso_graph P C) (listIso_graph P C) (listIso_graph P C)
    .unit (L₀).nil (Lists.nil ((F).obj C).obj) (fun _ => 0)
  · intro u z _
    exact SyntacticLists.nil_value 𝗣𝗔 ℕ (⊤_ (PredicateCategory 𝗣𝗔)) C z
  · intro u output
    exact Lists.nil_graph ((F).obj C).obj u output

private theorem source_cons_value (u : ℕ)
    (z : PredicateInterpretation.Obj ℕ (CategoryTheory.Limits.prod
      (C := PredicateCategory 𝗣𝗔) C (L₀).carrier))
    (hr : (baseRepresentation 𝗣𝗔 (L₀).carrier (L₀).carrier (.product (.coefficient C) .term)).val.Evalb
      (M := ℕ) ![u,z.val]) :
    (((PredicateInterpretation.functor 𝗣𝗔 ℕ).map (L₀).cons) z).val=
      adjoin (Nat.unpair u).1 (Nat.unpair u).2 := by
  obtain ⟨head,tail,hu,hh,ht⟩ :=
    (NumericalPolynomialRepresentation.representation_product_typed 𝗣𝗔 ℕ
      (L₀).carrier (L₀).carrier (.coefficient C) .term u z).mp hr
  have hh' := (baseRepresentation_coefficient_eval 𝗣𝗔 ℕ (L₀).carrier (L₀).carrier C head _).mp hh
  have ht' := (baseRepresentation_term_eval 𝗣𝗔 ℕ (L₀).carrier (L₀).carrier tail _).mp ht
  have hp : Nat.unpair u=(head,tail) := by
    simpa only [nat_pair_eq,Nat.unpair_pair] using congrArg Nat.unpair hu
  exact (SyntacticLists.cons_value 𝗣𝗔 ℕ C z).trans
    ((congrArg₂ adjoin hh'.2 ht'.2).trans
      (congrArg (fun n : ℕ × ℕ => adjoin n.1 n.2) hp).symm)

private theorem raw_cons_comparison :
    (inputIso P (L₀).carrier (L₀).carrier (L₁).carrier (L₁).carrier (listIso P C) (listIso P C)
      (.product (.coefficient C) .term)).hom ≫ (F).map (L₀).cons=
      Lists.adjoinMap ((F).obj C).obj ≫ (listIso P C).hom := by
  apply operation_square P (L₀).carrier (L₀).carrier (L₀).carrier
    (L₁).carrier (L₁).carrier (L₁).carrier (listIso P C) (listIso P C) (listIso P C)
    (listIso_graph P C) (listIso_graph P C) (listIso_graph P C)
    (.product (.coefficient C) .term) (L₀).cons (Lists.adjoinMap ((F).obj C).obj)
    (fun u => adjoin (Nat.unpair u).1 (Nat.unpair u).2)
  · exact source_cons_value C
  · intro u output
    change output∈Total.val (Lists.adjoinMap ((F).obj C).obj).hom u ↔
      ((Nat.unpair u).1∈((F).obj C).obj.support ∧
        (Nat.unpair u).2∈(Lists.carrier ((F).obj C).obj).support) ∧
        output=adjoin (Nat.unpair u).1 (Nat.unpair u).2
    simpa only [Nat.pair_unpair,and_assoc] using Lists.adjoin_graph ((F).obj C).obj (Nat.unpair u).1 (Nat.unpair u).2 output

theorem list_nil_comparison : (L₁).nil ≫ (listIso P C).hom=(mappedListAlgebra P C).nil := by
  have hId : (𝟙 (⊤_ (Total.TotalCategory P))) ≫ inv (terminalComparison (F)) = inv (terminalComparison (F)) :=
    Category.id_comp _
  apply (cancel_epi (Syntax.Raw.baseComparison (L₁).carrier (L₁).carrier .unit).hom).mp
  simpa only [directListAlgebra,inputIso,Syntax.Polynomial.mapped,SyntaxPolynomial.mapCoefficients,SyntaxPolynomial.eval,
    Syntax.Polynomial.component,Iso.trans_hom,Iso.trans_inv,Iso.symm_hom,asIso_inv,Functor.mapIso_hom,Functor.const_obj_map,
    Category.comp_id,Category.id_comp,Lists.algebra,Category.assoc,Iso.hom_inv_id_assoc,mappedListAlgebra,hId] using
    (raw_nil_comparison P C).symm

theorem list_cons_comparison :
    (L₁).cons ≫ (listIso P C).hom=
      prod.map (𝟙 ((F).obj C)) (listIso P C).hom ≫ (mappedListAlgebra P C).cons := by
  have hId : prod.map (𝟙 ((F).obj C)) (𝟙 ((F).obj (L₀).carrier)) ≫
      inv (prodComparison (F) C (L₀).carrier) = inv (prodComparison (F) C (L₀).carrier) := by
    exact (congrArg (fun k => k ≫ inv (prodComparison (F) C (L₀).carrier))
      (show prod.map (𝟙 ((F).obj C)) (𝟙 ((F).obj (L₀).carrier)) = 𝟙 _ from prod.map_id_id)).trans
        (Category.id_comp _)
  apply (cancel_epi (Syntax.Raw.baseComparison (L₁).carrier (L₁).carrier
    (Lists.consPolynomial ((F).obj C).obj)).hom).mp
  simpa only [directListAlgebra,inputIso,Syntax.Polynomial.mapped,SyntaxPolynomial.mapCoefficients,SyntaxPolynomial.eval,
    SyntaxPolynomial.productFunctor,Syntax.Polynomial.component,Iso.trans_hom,Iso.trans_inv,Iso.symm_hom,asIso_inv,
    Functor.mapIso_hom,prod.mapIso_inv,Functor.const_obj_obj,Functor.const_obj_map,Iso.refl_inv,Category.comp_id,
    prod.map_id_id,Category.id_comp,CategoryTheory.Prod.fst,CategoryTheory.Prod.snd,Lists.algebra,Lists.consPolynomial,Category.assoc,
    Iso.hom_inv_id_assoc,mappedListAlgebra,hId] using (raw_cons_comparison P C).symm

def listAlgebraIso : (L₁).asAlgebra ≅ (mappedListAlgebra P C).asAlgebra :=
  SyntacticLists.Transport.constructorsIso _ _ (listIso P C)
    (list_nil_comparison P C) (list_cons_comparison P C)

def mappedListInitial : IsInitial (mappedListAlgebra P C).asAlgebra :=
  (Lists.initial ((F).obj C).obj).ofIso (listAlgebraIso P C)

private def parameterListIso {D : Type*} [Category D] [HasFiniteLimits D] [HasFiniteCoproducts D]
    {U : D} (L B : ListAlgebra U) (i : L.carrier ≅ B.carrier)
    (hn : L.nil ≫ i.hom=B.nil) (hc : L.cons ≫ i.hom=prod.map (𝟙 U) i.hom ≫ B.cons)
    (R : D) : (L.withParameters R).asAlgebra ≅ (B.withParameters R).asAlgebra := by
  let k : constantFamily R L.carrier ⟶ constantFamily R B.carrier :=
    ((constantFamilyFunctor R).mapIso i).hom
  apply SyntacticLists.Transport.constructorsIso _ _ ((constantFamilyFunctor R).mapIso i)
  · apply Over.OverMorphism.ext
    apply prod.hom_ext
    · exact (Over.w ((L.withParameters R).nil ≫ k)).trans (Over.w (B.withParameters R).nil).symm
    · change (prod.lift (⊤_ (Over R)).hom (terminal.from (⊤_ (Over R)).left ≫ L.nil) ≫
        prod.map (𝟙 R) i.hom) ≫ prod.snd =
          prod.lift (⊤_ (Over R)).hom (terminal.from (⊤_ (Over R)).left ≫ B.nil) ≫ prod.snd
      rw [Category.assoc,prod.map_snd,← Category.assoc,prod.lift_snd,prod.lift_snd,Category.assoc,hn]
  · apply Over.OverMorphism.ext
    apply prod.hom_ext
    · exact (Over.w ((L.withParameters R).cons ≫ k)).trans
        (Over.w (prod.map (𝟙 (constantFamily R U)) k ≫ (B.withParameters R).cons)).symm
    · let A₀ := constantFamily R U
      let LA := constantFamily R L.carrier
      let B₀ := constantFamily R B.carrier
      let m : A₀ ⨯ LA ⟶ A₀ ⨯ B₀ := prod.map (𝟙 A₀) k
      let hL : (A₀ ⨯ LA).left ⟶ U ⨯ L.carrier := prod.lift
        ((prod.fst : A₀ ⨯ LA ⟶ A₀).left ≫ prod.snd)
        ((prod.snd : A₀ ⨯ LA ⟶ LA).left ≫ prod.snd)
      let hB : (A₀ ⨯ B₀).left ⟶ U ⨯ B.carrier := prod.lift
        ((prod.fst : A₀ ⨯ B₀ ⟶ A₀).left ≫ prod.snd)
        ((prod.snd : A₀ ⨯ B₀ ⟶ B₀).left ≫ prod.snd)
      change (prod.lift (A₀ ⨯ LA).hom (hL ≫ L.cons) ≫ prod.map (𝟙 R) i.hom) ≫ prod.snd =
        (m.left ≫ prod.lift (A₀ ⨯ B₀).hom (hB ≫ B.cons)) ≫ prod.snd
      rw [Category.assoc,prod.map_snd,← Category.assoc,prod.lift_snd,
        Category.assoc,hc,Category.assoc,prod.lift_snd]
      rw [← Category.assoc hL (prod.map (𝟙 U) i.hom) B.cons,
        ← Category.assoc m.left hB B.cons]
      apply congrArg (fun f => f ≫ B.cons)
      apply prod.hom_ext
      · have hf : m.left ≫ (prod.fst : A₀ ⨯ B₀ ⟶ A₀).left =
            (prod.fst : A₀ ⨯ LA ⟶ A₀).left := by
          simpa only [Over.comp_left,Over.id_left,Category.comp_id] using
            congrArg Over.Hom.left (prod.map_fst (W := A₀) (X := LA) (Y := A₀) (Z := B₀) (𝟙 A₀) k)
        calc
          _ = (prod.fst : A₀ ⨯ LA ⟶ A₀).left ≫ prod.snd := by
            simp only [hL,Category.assoc,prod.map_fst,Category.comp_id,prod.lift_fst]
          _ = m.left ≫ (prod.fst : A₀ ⨯ B₀ ⟶ A₀).left ≫ prod.snd := by
            simpa only [Category.assoc] using congrArg (fun f => f ≫ (prod.snd : R ⨯ U ⟶ U)) hf.symm
          _ = _ := by simp only [hB,Category.assoc,prod.lift_fst]
      · have hs : m.left ≫ (prod.snd : A₀ ⨯ B₀ ⟶ B₀).left =
            (prod.snd : A₀ ⨯ LA ⟶ LA).left ≫ k.left := by
          exact congrArg Over.Hom.left (prod.map_snd (W := A₀) (X := LA) (Y := A₀) (Z := B₀) (𝟙 A₀) k)
        calc
          _ = (prod.snd : A₀ ⨯ LA ⟶ LA).left ≫ prod.snd ≫ i.hom := by
            have hp : hL ≫ prod.snd = (prod.snd : A₀ ⨯ LA ⟶ LA).left ≫ prod.snd :=
              prod.lift_snd _ _
            rw [Category.assoc,prod.map_snd,← Category.assoc]
            simpa only [Category.assoc] using congrArg (fun f => f ≫ i.hom) hp
          _ = (prod.snd : A₀ ⨯ LA ⟶ LA).left ≫ k.left ≫ prod.snd := by
            simp only [k,Functor.mapIso_hom,constantFamilyFunctor,Over.homMk_left,prod.map_snd]
          _ = m.left ≫ (prod.snd : A₀ ⨯ B₀ ⟶ B₀).left ≫ prod.snd := by
            simpa only [Category.assoc] using
              congrArg (fun f => f ≫ (prod.snd : R ⨯ B.carrier ⟶ B.carrier)) hs.symm
          _ = _ := by simp only [hB,Category.assoc,prod.lift_snd]

def mappedListStable : StableListAlgebra ((F).obj C) where
  algebra := mappedListAlgebra P C
  initial := mappedListInitial P C
  stable R := (Lists.withParametersInitial R ((F).obj C).obj).ofIso
    (parameterListIso (L₁) (mappedListAlgebra P C) (listIso P C)
      (list_nil_comparison P C) (list_cons_comparison P C) R)

end CategoricalEssentialIncompleteness.V46.Miller.NamedSyntaxComparison
