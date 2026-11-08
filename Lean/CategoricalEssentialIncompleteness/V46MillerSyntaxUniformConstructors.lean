/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46MillerSyntaxUniformFold
import CategoricalEssentialIncompleteness.V46MillerSyntaxCarrierConstructors

/-! # Constructor equations for arbitrary uniformly enumerable coefficients

The finite polynomial retains each actual coefficient predicate. Only
the auxiliary numerical parser forgets predicates, and its graph equality
is proved. All target operation values are supplied by actual slice
morphisms and occur positively in the selected finite records.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FailureOfComposition.CodedObjectMembership
namespace CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
open SyntacticSyntax SyntacticSyntax.Coding SyntacticSyntax.NatVectors
variable {P : Uniform.Family} {R : Total.TotalCategory P} {X Y : Over R}
variable {p q : SyntaxPolynomial (Total.TotalCategory P)}
variable (hT : object R X Y p ⟶ X) (hF : object R X Y q ⟶ Y)

def UniformMapValues : SyntaxPolynomial (Total.TotalCategory P) → ℕ → ℕ → ℕ → Prop
  | .term,r,u,v => r ∈ R.obj.support ∧ u ∈ (uniformWords false p q).support ∧
      adjoin (Nat.pair v 0) 0+1 ∈ evaluation hT hF (Nat.pair r u)
  | .formula,r,u,v => r ∈ R.obj.support ∧ u ∈ (uniformWords true p q).support ∧
      adjoin (Nat.pair v 1) 0+1 ∈ evaluation hT hF (Nat.pair r u)
  | .coefficient C,r,u,v => r ∈ R.obj.support ∧ u ∈ C.obj.support ∧ v=u
  | .unit,r,u,v => r ∈ R.obj.support ∧ u=0 ∧ v=0
  | .product a b,r,u,v =>
      UniformMapValues a r (Nat.unpair u).1 (Nat.unpair v).1 ∧
      UniformMapValues b r (Nat.unpair u).2 (Nat.unpair v).2
  | .sum a b,r,u,v =>
      ((Nat.unpair u).2=0 ∧ (Nat.unpair v).2=0 ∧ UniformMapValues a r (Nat.unpair u).1 (Nat.unpair v).1) ∨
      ((Nat.unpair u).2=1 ∧ (Nat.unpair v).2=1 ∧ UniformMapValues b r (Nat.unpair u).1 (Nat.unpair v).1)

theorem uniformMapValues_parameter (Q : SyntaxPolynomial (Total.TotalCategory P)) {r u v : ℕ}
    (h : UniformMapValues hT hF Q r u v) : r ∈ R.obj.support := by
  induction Q generalizing u v with
  | term => exact h.1
  | formula => exact h.1
  | coefficient _ => exact h.1
  | unit => exact h.1
  | product _ _ ih _ => exact ih h.1
  | sum _ _ il ir => exact h.elim (fun h => il h.2.2) (fun h => ir h.2.2)

theorem uniformMapValues_shape (Q : SyntaxPolynomial (Total.TotalCategory P)) {r u v : ℕ}
    (h : UniformMapValues hT hF Q r u v) : shape (skeleton Q) u=shape (skeleton Q) v := by
  induction Q generalizing u v with
  | term => rfl
  | formula => rfl
  | coefficient _ => simpa [skeleton,SyntaxPolynomial.mapCoefficients,shape] using h.2.2.symm
  | unit => rfl
  | product a b ia ib =>
      simpa only [skeleton,SyntaxPolynomial.mapCoefficients,shape,FiniteSigmaOne.nat_pi₁_eq,NatVectors.nat_pi₂_eq] using
        congrArg₂ (fun x y : ℕ => Arithmetic.pair x y) (ia h.1) (ib h.2)
  | sum a b ia ib =>
      rcases h with ⟨hu,hv,hm⟩ | ⟨hu,hv,hm⟩
      · simpa [skeleton,SyntaxPolynomial.mapCoefficients,shape,FiniteSigmaOne.nat_pi₁_eq,NatVectors.nat_pi₂_eq,hu,hv] using
          congrArg (fun x : ℕ => Arithmetic.pair x 0) (ia hm)
      · simpa [skeleton,SyntaxPolynomial.mapCoefficients,shape,FiniteSigmaOne.nat_pi₁_eq,NatVectors.nat_pi₂_eq,hu,hv] using
          congrArg (fun x : ℕ => Arithmetic.pair x 1) (ib hm)

theorem uniformMapValues_source (Q : SyntaxPolynomial (Total.TotalCategory P)) {r u v : ℕ}
    (h : UniformMapValues hT hF Q r u v) :
    u ∈ (carrier (uniformWords false p q) (uniformWords true p q) Q).support := by
  induction Q generalizing u v with
  | term => exact h.2.1
  | formula => exact h.2.1
  | coefficient _ => exact h.2.1
  | unit => exact h.2.1
  | product _ _ ia ib => exact ⟨ia h.1,ib h.2⟩
  | sum _ _ ia ib => exact h.elim (fun h => Or.inl ⟨h.1,ia h.2.2⟩) (fun h => Or.inr ⟨h.1,ib h.2.2⟩)

theorem uniformMapValues_fiber (Q : SyntaxPolynomial (Total.TotalCategory P)) {r u v : ℕ}
    (h : UniformMapValues hT hF Q r u v) : fiber R X Y Q (r,v) := by
  induction Q generalizing u v with
  | term =>
      exact uniformSelectedValue_fiber hT hF false h.1 h.2.1
        ((Part.mem_map_iff _).mpr ⟨_,h.2.2,extract_singleton false v⟩)
  | formula =>
      exact uniformSelectedValue_fiber hT hF true h.1 h.2.1
        ((Part.mem_map_iff _).mpr ⟨_,h.2.2,extract_singleton true v⟩)
  | coefficient _ => exact ⟨h.1,h.2.2.symm ▸ h.2.1⟩
  | unit => exact ⟨h.1,h.2.2⟩
  | product _ _ ia ib => exact ⟨ia h.1,ib h.2⟩
  | sum _ _ ia ib => exact h.elim (fun h => Or.inl ⟨h.2.1,ia h.2.2⟩) (fun h => Or.inr ⟨h.2.1,ib h.2.2⟩)

theorem uniformMapValues_exists (Q : SyntaxPolynomial (Total.TotalCategory P)) {r u : ℕ}
    (hr : r ∈ R.obj.support)
    (hu : u ∈ (carrier (uniformWords false p q) (uniformWords true p q) Q).support) :
    ∃ v,UniformMapValues hT hF Q r u v := by
  induction Q generalizing u with
  | term =>
      obtain ⟨s,hs⟩ := Part.dom_iff_mem.mp
        (evaluation_total hT hF (uniformWords_coefficientWord false p q r u hr hu))
      obtain ⟨v,hv⟩ := uniformWords_singleton hT hF false hu hs
      exact ⟨v,hr,hu,hv ▸ hs⟩
  | formula =>
      obtain ⟨s,hs⟩ := Part.dom_iff_mem.mp
        (evaluation_total hT hF (uniformWords_coefficientWord true p q r u hr hu))
      obtain ⟨v,hv⟩ := uniformWords_singleton hT hF true hu hs
      exact ⟨v,hr,hu,hv ▸ hs⟩
  | coefficient _ => exact ⟨u,hr,hu,rfl⟩
  | unit => exact ⟨0,hr,hu,rfl⟩
  | product a b ia ib =>
      obtain ⟨v,hv⟩ := ia hu.1
      obtain ⟨w,hw⟩ := ib hu.2
      exact ⟨Nat.pair v w,by simpa [UniformMapValues] using And.intro hv hw⟩
  | sum a b ia ib =>
      rcases hu with ⟨hk,hu⟩ | ⟨hk,hu⟩
      · obtain ⟨v,hv⟩ := ia hu
        refine ⟨Nat.pair v 0,?_⟩
        change (_ ∧ _ ∧ _) ∨ (_ ∧ _ ∧ _)
        apply Or.inl
        refine ⟨hk,?_,?_⟩
        · simp only [Nat.unpair_pair]
        · simpa only [Nat.unpair_pair] using hv
      · obtain ⟨v,hv⟩ := ib hu
        refine ⟨Nat.pair v 1,?_⟩
        change (_ ∧ _ ∧ _) ∨ (_ ∧ _ ∧ _)
        apply Or.inr
        refine ⟨hk,?_,?_⟩
        · simp only [Nat.unpair_pair]
        · simpa only [Nat.unpair_pair] using hv

theorem uniformMapValues_target_erased (Q : SyntaxPolynomial (Total.TotalCategory P)) {r u v : ℕ}
    (h : UniformMapValues hT hF Q r u v) :
    (SyntacticSyntax.rawCarrier topCarrier topCarrier (erased Q)).val.Evalb (M := ℕ) ![v] := by
  induction Q generalizing u v with
  | term => simp [erased,skeleton,SyntaxPolynomial.mapCoefficients,SyntacticSyntax.rawCarrier,topCarrier]
  | formula => simp [erased,skeleton,SyntaxPolynomial.mapCoefficients,SyntacticSyntax.rawCarrier,topCarrier]
  | coefficient _ => simp [erased,skeleton,SyntaxPolynomial.mapCoefficients,SyntacticSyntax.rawCarrier,topCarrier]
  | unit => simpa [erased,skeleton,SyntaxPolynomial.mapCoefficients,SyntacticSyntax.rawCarrier] using h.2.2
  | product a b ia ib =>
      exact (SyntacticSyntax.rawCarrier_product_eval _ _ (erased a) (erased b) v).mpr
        ⟨(Nat.unpair v).1,(Nat.unpair v).2,by simp [nat_pair_eq],ia h.1,ib h.2⟩
  | sum a b ia ib =>
      rcases h with ⟨_,hk,hm⟩ | ⟨_,hk,hm⟩
      · exact (SyntacticSyntax.rawCarrier_sum_eval _ _ (erased a) (erased b) v).mpr
          (Or.inl ⟨(Nat.unpair v).1,by simpa only [nat_pair_eq,hk] using (Nat.pair_unpair v).symm,ia hm⟩)
      · exact (SyntacticSyntax.rawCarrier_sum_eval _ _ (erased a) (erased b) v).mpr
          (Or.inr ⟨(Nat.unpair v).1,by simpa only [nat_pair_eq,hk] using (Nat.pair_unpair v).symm,ib hm⟩)

theorem childStack_guard_map (f : SyntacticPredicates.Carrier → SyntacticPredicates.Carrier)
    (Q : SyntacticSyntax.RawPolynomial) (v tail : ℕ) :
    childStack (Q.mapCoefficients f) v tail=childStack Q v tail := by
  induction Q generalizing v tail with
  | term => rfl
  | formula => rfl
  | coefficient _ => rfl
  | unit => rfl
  | product a b ia ib => simp only [SyntaxPolynomial.mapCoefficients,childStack,ia,ib]
  | sum a b ia ib =>
      simp only [SyntaxPolynomial.mapCoefficients,childStack,ia,ib]
      by_cases h : π₂ v = 0 <;> simp [h]

theorem refill_guard_map (f : SyntacticPredicates.Carrier → SyntacticPredicates.Carrier)
    (Q : SyntacticSyntax.RawPolynomial) (s stack : ℕ) :
    Coding.refill (Q.mapCoefficients f) s stack=Coding.refill Q s stack := by
  have he := (Coding.refillGraph_eval Q (Coding.refill Q s stack) s stack).mpr rfl
  have hm : (Coding.refillGraph (Q.mapCoefficients f)).val.Evalb (M := ℕ) ![Coding.refill Q s stack,s,stack] := by
    simpa only [NumericalDerivationInterpretation.Parser.refillGraph_map] using he
  exact ((Coding.refillGraph_eval _ _ _ _).mp hm).symm

theorem uniform_children_trace (Q : SyntaxPolynomial (Total.TotalCategory P)) {r u v : ℕ}
    (hm : UniformMapValues hT hF Q r u v) (tail : ℕ) :
    Trace hT hF r (Nat.natToList (childrenWord (skeleton Q) u))
      (tail+1) (childStack (skeleton Q) v tail+1) := by
  induction Q generalizing u v tail with
  | term =>
      have ht := (evaluation_trace hT hF r u _).mp hm.2.2
      simpa [skeleton,SyntaxPolynomial.mapCoefficients,childrenWord,childStack,frameStatus_succ,frameStatus,nat_pair_eq] using
        Trace.frame hT hF ht (by simp) tail
  | formula =>
      have ht := (evaluation_trace hT hF r u _).mp hm.2.2
      simpa [skeleton,SyntaxPolynomial.mapCoefficients,childrenWord,childStack,frameStatus_succ,frameStatus,nat_pair_eq] using
        Trace.frame hT hF ht (by simp) tail
  | coefficient _ => simpa [skeleton,SyntaxPolynomial.mapCoefficients,childrenWord,childStack,Nat.natToList] using
      (Trace.nil (hT := hT) (hF := hF) (r := r) (tail+1))
  | unit => simpa [skeleton,SyntaxPolynomial.mapCoefficients,childrenWord,childStack,Nat.natToList] using
      (Trace.nil (hT := hT) (hF := hF) (r := r) (tail+1))
  | product a b ia ib =>
      have ht := Trace.append hT hF (ia hm.1 tail)
        (ib hm.2 (childStack (skeleton a) (Nat.unpair v).1 tail))
      simpa only [skeleton,SyntaxPolynomial.mapCoefficients,childrenWord,childStack,
        FiniteSigmaOne.nat_pi₁_eq,NatVectors.nat_pi₂_eq,natToList_append] using ht
  | sum a b ia ib =>
      rcases hm with ⟨hu,hv,hm⟩ | ⟨hu,hv,hm⟩
      · simpa [skeleton,SyntaxPolynomial.mapCoefficients,childrenWord,childStack,
          FiniteSigmaOne.nat_pi₁_eq,NatVectors.nat_pi₂_eq,hu,hv] using ia hm tail
      · simpa [skeleton,SyntaxPolynomial.mapCoefficients,childrenWord,childStack,
          FiniteSigmaOne.nat_pi₁_eq,NatVectors.nat_pi₂_eq,hu,hv] using ib hm tail

theorem uniform_root_valueStep (formula : Bool) (r u v value : ℕ)
    (hm : UniformMapValues hT hF (if formula then q else p) r u v)
    (hop : value ∈ (if formula then operation hF else operation hT) (r,v)) :
    adjoin (Nat.pair value (if formula then 1 else 0)) 0+1 ∈ valueStep hT hF
      (r,(Nat.pair (shape (skeleton (if formula then q else p)) u) (if formula then 1 else 0),
        childStack (skeleton (if formula then q else p)) v 0+1)) := by
  have hs := uniformMapValues_shape hT hF (if formula then q else p) hm
  have ht := uniformMapValues_target_erased hT hF (if formula then q else p) hm
  have hr := Coding.refill_shape (erased (if formula then q else p)) v 0 ht
  simp only [erased,NumericalDerivationInterpretation.Parser.shape_map,childStack_guard_map,refill_guard_map] at hr
  rw [← hs] at hr
  cases formula
  · simp only [valueStep,Nat.add_one_ne_zero,ite_false,Nat.unpair_pair,Nat.add_sub_cancel]
    exact (outcome_graph hT false r (shape (skeleton p) u) (childStack (skeleton p) v 0) _).mpr
      (Or.inr ⟨v,0,value,hr,hop,rfl⟩)
  · simp only [valueStep,Nat.add_one_ne_zero,ite_false,Nat.unpair_pair,ite_true,Nat.add_sub_cancel]
    exact (outcome_graph hF true r (shape (skeleton q) u) (childStack (skeleton q) v 0) _).mpr
      (Or.inr ⟨v,0,value,hr,hop,rfl⟩)

theorem uniform_evaluation_of_mapValues (formula : Bool) (r u v value : ℕ)
    (hm : UniformMapValues hT hF (if formula then q else p) r u v)
    (hop : value ∈ (if formula then operation hF else operation hT) (r,v)) :
    adjoin (Nat.pair value (if formula then 1 else 0)) 0+1 ∈ evaluation hT hF
      (Nat.pair r (constructor formula (skeleton (if formula then q else p)) u)) := by
  have hc := uniform_children_trace hT hF (if formula then q else p) hm 0
  have hr := uniform_root_valueStep hT hF formula r u v value hm hop
  have ht : Trace hT hF r [Nat.pair (shape (skeleton (if formula then q else p)) u) (if formula then 1 else 0)]
      (childStack (skeleton (if formula then q else p)) v 0+1)
      (adjoin (Nat.pair value (if formula then 1 else 0)) 0+1) := .cons hr (.nil _)
  apply (evaluation_trace hT hF r _ _).mpr
  simpa only [constructor,natToList_concat,nat_pair_eq,zero_add] using Trace.append hT hF hc ht

theorem uniform_evaluation_constructor (formula : Bool) (r u value : ℕ)
    (hr : r ∈ R.obj.support)
    (hu : u ∈ (carrier (uniformWords false p q) (uniformWords true p q) (if formula then q else p)).support) :
    (adjoin (Nat.pair value (if formula then 1 else 0)) 0+1 ∈ evaluation hT hF
      (Nat.pair r (constructor formula (skeleton (if formula then q else p)) u)) ↔
      ∃ v,UniformMapValues hT hF (if formula then q else p) r u v ∧
        value ∈ (if formula then operation hF else operation hT) (r,v)) := by
  constructor
  · intro he
    obtain ⟨v,hm⟩ := uniformMapValues_exists hT hF (if formula then q else p) hr hu
    have hf := uniformMapValues_fiber hT hF (if formula then q else p) hm
    have htotal : ∃ output,output ∈ (if formula then operation hF else operation hT) (r,v) := by
      cases formula
      · exact operation_exists hT hf
      · exact operation_exists hF hf
    obtain ⟨output,hop⟩ := htotal
    have hout := uniform_evaluation_of_mapValues hT hF formula r u v output hm hop
    have heq : value=output := by
      have he := Part.mem_unique he hout
      have hb := ((adjoin_inj _ _ _ _).mp (Nat.add_right_cancel he)).1
      simpa only [Nat.unpair_pair] using congrArg (fun n => (Nat.unpair n).1) hb
    exact ⟨v,hm,heq.symm ▸ hop⟩
  · rintro ⟨v,hm,hop⟩
    exact uniform_evaluation_of_mapValues hT hF formula r u v value hm hop

theorem uniformFold_constructor (formula : Bool) (r u value : ℕ)
    (hr : r ∈ R.obj.support)
    (hu : u ∈ (carrier (uniformWords false p q) (uniformWords true p q) (if formula then q else p)).support) :
    (value ∈ Total.val (uniformFold hT hF formula).left.hom
      (Nat.pair r (constructor formula (skeleton (if formula then q else p)) u)) ↔
      ∃ v,UniformMapValues hT hF (if formula then q else p) r u v ∧
        value ∈ (if formula then operation hF else operation hT) (r,v)) := by
  have hw := uniformWords_constructor p q formula hu
  rw [uniformFold_graph]
  simp only [hr,hw,true_and]
  exact uniform_evaluation_constructor hT hF formula r u value hr hu

end CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
