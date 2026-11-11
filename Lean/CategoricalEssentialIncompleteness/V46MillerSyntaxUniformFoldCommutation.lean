/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerSyntaxUniformLiftedAction
public import CategoricalEssentialIncompleteness.V46MillerSyntaxUniformFoldUnique

/-! # Constructor commutation of the actual uniform fold

The input is an arbitrary actual raw family, including the external
parameter at each recursive leaf. The equation concerns the constructed
polynomial morphism and the constructed literal family constructor.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
open SyntacticSyntax SyntacticSyntax.Coding
variable {P : Uniform.Family} {R : Total.TotalCategory P} {X Y : Over R}
variable {p q : SyntaxPolynomial (Total.TotalCategory P)}
variable (hT : object R X Y p ⟶ X) (hF : object R X Y q ⟶ Y)

def chosenOperation : (formula : Bool) → object R X Y (if formula then q else p) ⟶
    (if formula then Y else X)
  | false => hT
  | true => hF

theorem mapValues_of_erased (Q : SyntaxPolynomial (Total.TotalCategory P)) {r u v : ℕ}
    (hr : r∈R.obj.support)
    (hu : u∈(carrier (uniformWords false p q) (uniformWords true p q) Q).support)
    (h : Relations.map (fun r => r∈R.obj.support) (foldRelation hT hF) (erased Q) r u v) :
    UniformMapValues hT hF Q r u v := by
  induction Q generalizing u v with
  | term => exact (uniformFold_graph hT hF false r u v).mp h
  | formula => exact (uniformFold_graph hT hF true r u v).mp h
  | coefficient C => exact ⟨hr,hu,h.2.2⟩
  | unit => exact h
  | product a b ia ib =>
    have h' : Relations.map (fun r => r∈R.obj.support) (foldRelation hT hF)
        (erased a) r (Nat.unpair u).1 (Nat.unpair v).1 ∧
      Relations.map (fun r => r∈R.obj.support) (foldRelation hT hF)
        (erased b) r (Nat.unpair u).2 (Nat.unpair v).2 := by
      simpa only [erased,skeleton,SyntaxPolynomial.mapCoefficients,Relations.map,
        FiniteSigmaOne.nat_pi₁_eq,NatVectors.nat_pi₂_eq] using h
    exact ⟨ia hu.1 h'.1,ib hu.2 h'.2⟩
  | sum a b ia ib =>
    have h' : ((Nat.unpair u).2=0 ∧ (Nat.unpair v).2=0 ∧
        Relations.map (fun r => r∈R.obj.support) (foldRelation hT hF)
          (erased a) r (Nat.unpair u).1 (Nat.unpair v).1) ∨
      ((Nat.unpair u).2=1 ∧ (Nat.unpair v).2=1 ∧
        Relations.map (fun r => r∈R.obj.support) (foldRelation hT hF)
          (erased b) r (Nat.unpair u).1 (Nat.unpair v).1) := by
      simpa only [erased,skeleton,SyntaxPolynomial.mapCoefficients,Relations.map,
        FiniteSigmaOne.nat_pi₁_eq,NatVectors.nat_pi₂_eq] using h
    rcases hu with ⟨hu0,ha⟩ | ⟨hu1,hb⟩
    · rcases h' with ⟨_,hv,hm⟩ | ⟨hu1,_,_⟩
      · exact Or.inl ⟨hu0,hv,ia ha hm⟩
      · omega
    · rcases h' with ⟨hu0,_,_⟩ | ⟨_,hv,hm⟩
      · omega
      · exact Or.inr ⟨hu1,hv,ib hb hm⟩

theorem foldAction_mapValues (Q : SyntaxPolynomial (Total.TotalCategory P)) {r u v : ℕ}
    (hr : r∈R.obj.support)
    (hu : u∈(carrier (uniformWords false p q) (uniformWords true p q) Q).support)
    (h : ActionGraph R (uniformWordFamily R false p q) (uniformWordFamily R true p q)
      X Y (uniformFold hT hF false) (uniformFold hT hF true)
      Q r (constantLift Q r u) v) : UniformMapValues hT hF Q r u v := by
  apply mapValues_of_erased hT hF Q hr hu
  have hm := (liftedAction_graph (uniformFold hT hF false) (uniformFold hT hF true)
    Q r u v hr hu).mp h
  have hc : candidateRelation (uniformFold hT hF false) (uniformFold hT hF true) =
      foldRelation hT hF := by
    funext formula r word value
    cases formula <;> rfl
  simpa only [hc] using hm

theorem uniformFold_raw_commutes (formula : Bool) :
    rawAction R (uniformWordFamily R false p q) (uniformWordFamily R true p q)
      X Y (uniformFold hT hF false) (uniformFold hT hF true)
      (if formula then q else p) ≫ chosenOperation hT hF formula =
      parameterConstructor R p q formula ≫ uniformFold hT hF formula := by
  apply Over.OverMorphism.ext
  apply WideSubcategory.hom_ext
  apply Total.val_ext_on_source
  intro n hn
  let Q := if formula then q else p
  let r := (Nat.unpair n).1
  let u := constantUnlift Q (Nat.unpair n).2
  have hs : fiber R (constantObject R (wordObject false p q))
      (constantObject R (wordObject true p q)) Q (Nat.unpair n) := hn
  obtain ⟨hr,hu⟩ := constantUnlift_supported R (wordObject false p q) (wordObject true p q) Q hs
  have hrestore : constantLift Q r u=(Nat.unpair n).2 :=
    constantLift_unlift R (wordObject false p q) (wordObject true p q) Q hs
  let left := rawAction R (uniformWordFamily R false p q) (uniformWordFamily R true p q)
    X Y (uniformFold hT hF false) (uniformFold hT hF true) Q ≫ chosenOperation hT hF formula
  obtain ⟨value,hvalue⟩ := Part.dom_iff_mem.mp
    ((Total.total_iff left.left.hom).mp left.left.property n hn)
  obtain ⟨m,hm,hop⟩ := (Total.mem_val_comp _ _ n value).mp hvalue
  have hm' : m∈Total.val (rawAction R (uniformWordFamily R false p q)
      (uniformWordFamily R true p q) X Y (uniformFold hT hF false)
      (uniformFold hT hF true) Q).left.hom (Nat.pair r (constantLift Q r u)) := by
    simpa only [hrestore,r,Nat.pair_unpair] using hm
  have hg := (rawAction_graph R (uniformWordFamily R false p q)
    (uniformWordFamily R true p q) X Y (uniformFold hT hF false)
    (uniformFold hT hF true) Q r (constantLift Q r u)
    (Nat.unpair m).1 (Nat.unpair m).2).mp (by simpa only [Nat.pair_unpair] using hm')
  have hmap := foldAction_mapValues hT hF Q hr hu hg.2
  have hopen : value∈(if formula then operation hF else operation hT)
      (r,(Nat.unpair m).2) := by
    have hmcode : Nat.pair r (Nat.unpair m).2=m := by
      rw [← hg.1,Nat.pair_unpair]
    cases formula <;> simpa [chosenOperation,operation,hmcode] using hop
  have hfold := (uniformFold_constructor hT hF formula r u value hr hu).mpr
    ⟨(Nat.unpair m).2,hmap,hopen⟩
  have hc : Nat.pair r (constructor formula (skeleton Q) u) ∈
      Total.val (parameterConstructor R p q formula).left.hom n := by
    have hc' := (parameterConstructor_graph R p q formula r (Nat.unpair n).2
      (Nat.pair r (constructor formula (skeleton Q) u))).mpr ⟨hs,rfl⟩
    simpa only [r,Nat.pair_unpair] using hc'
  have hright := (Total.mem_val_comp (parameterConstructor R p q formula).left.hom
    (uniformFold hT hF formula).left.hom n value).mpr ⟨_,hc,hfold⟩
  exact (Part.eq_some_iff.mpr hvalue).trans (Part.eq_some_iff.mpr hright).symm

end CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
