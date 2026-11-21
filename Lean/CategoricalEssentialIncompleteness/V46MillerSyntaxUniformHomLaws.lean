/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerSyntaxUniformLiftedAction
public import CategoricalEssentialIncompleteness.V46MillerSyntaxUniformFoldUnique

/-! # Constructor laws for every morphism from the word algebra

The candidate relation is the graph of the supplied algebra morphism. Its guarded root
law follows from that morphism's constructor equation, the polynomial chart
naturality, and the constructor graph. The target coefficient objects and parameter
families remain arbitrary.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory
namespace CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
open SyntacticSyntax SyntacticSyntax.Coding
variable {P : Uniform.Family} {R : Total.TotalCategory P}
  {p q : SyntaxPolynomial (Total.TotalCategory P)}

def algebraTermOperation (B : Endofunctor.Algebra
    (SyntaxPolynomial.jointFunctor (p.withParameters R) (q.withParameters R))) :
    object R B.a.1 B.a.2 p ⟶ B.a.1 :=
  (comparison R B.a.1 B.a.2 p).hom ≫ B.str.1

def algebraFormulaOperation (B : Endofunctor.Algebra
    (SyntaxPolynomial.jointFunctor (p.withParameters R) (q.withParameters R))) :
    object R B.a.1 B.a.2 q ⟶ B.a.2 :=
  (comparison R B.a.1 B.a.2 q).hom ≫ B.str.2

variable (B : Endofunctor.Algebra
  (SyntaxPolynomial.jointFunctor (p.withParameters R) (q.withParameters R)))
variable (f : Endofunctor.Algebra.Hom (parameterWordAlgebra R p q) B)

theorem algebraHom_raw_term_constructor :
    rawAction R (uniformWordFamily R false p q) (uniformWordFamily R true p q)
      B.a.1 B.a.2 f.f.1 f.f.2 p ≫ algebraTermOperation B =
      parameterConstructor R p q false ≫ f.f.1 := by
  have hf : (p.withParameters R).eval.map f.f ≫ B.str.1 =
      (parameterWordAlgebra R p q).str.1 ≫ f.f.1 := congrArg Prod.fst f.h
  change rawAction R (uniformWordFamily R false p q) (uniformWordFamily R true p q)
    B.a.1 B.a.2 f.f.1 f.f.2 p ≫ ((comparison R B.a.1 B.a.2 p).hom ≫ B.str.1) = _
  rw [← Category.assoc,rawAction_comparison,Category.assoc]
  change (comparison R (uniformWordFamily R false p q) (uniformWordFamily R true p q) p).hom ≫
    ((p.withParameters R).eval.map f.f ≫ B.str.1) = _
  rw [hf,← Category.assoc,parameterWordAlgebra_term_constructor]

theorem algebraHom_raw_formula_constructor :
    rawAction R (uniformWordFamily R false p q) (uniformWordFamily R true p q)
      B.a.1 B.a.2 f.f.1 f.f.2 q ≫ algebraFormulaOperation B =
      parameterConstructor R p q true ≫ f.f.2 := by
  have hf : (q.withParameters R).eval.map f.f ≫ B.str.2 =
      (parameterWordAlgebra R p q).str.2 ≫ f.f.2 := congrArg Prod.snd f.h
  change rawAction R (uniformWordFamily R false p q) (uniformWordFamily R true p q)
    B.a.1 B.a.2 f.f.1 f.f.2 q ≫ ((comparison R B.a.1 B.a.2 q).hom ≫ B.str.2) = _
  rw [← Category.assoc,rawAction_comparison,Category.assoc]
  change (comparison R (uniformWordFamily R false p q) (uniformWordFamily R true p q) q).hom ≫
    ((q.withParameters R).eval.map f.f ≫ B.str.2) = _
  rw [hf,← Category.assoc,parameterWordAlgebra_formula_constructor]

omit B f in
private theorem constructor_factorization {X Y Z : Over R}
    (f : uniformWordFamily R false p q ⟶ X)
    (g : uniformWordFamily R true p q ⟶ Y) (formula : Bool)
    (h : object R X Y (if formula then q else p) ⟶ Z)
    (k : uniformWordFamily R formula p q ⟶ Z)
    (hk : rawAction R (uniformWordFamily R false p q) (uniformWordFamily R true p q)
      X Y f g (if formula then q else p) ≫ h = parameterConstructor R p q formula ≫ k)
    (r u value : ℕ)
    (hu : u ∈ (carrier (uniformWords false p q) (uniformWords true p q)
      (if formula then q else p)).support)
    (hv : value ∈ Total.val k.left.hom
      (Nat.pair r (constructor formula (skeleton (if formula then q else p)) u))) :
    ∃ v,Relations.map (fun r => r∈R.obj.support) (candidateRelation f g)
      (erased (if formula then q else p)) r u v ∧ value ∈ operation h (r,v) := by
  have hs := Total.val_source k.left.hom _ _ hv
  have hr : r ∈ R.obj.support := by
    change (Nat.unpair (Nat.pair r
      (constructor formula (skeleton (if formula then q else p)) u))).1 ∈ R.obj.support ∧
      (Nat.unpair (Nat.pair r
        (constructor formula (skeleton (if formula then q else p)) u))).2 ∈
          (uniformWords formula p q).support at hs
    simpa only [Nat.unpair_pair] using hs.1
  have hsource : fiber R (uniformWordFamily R false p q) (uniformWordFamily R true p q)
      (if formula then q else p) (r,constantLift (if formula then q else p) r u) :=
    constantLift_supported R (wordObject false p q) (wordObject true p q)
      (if formula then q else p) hr hu
  have hc : Nat.pair r (constructor formula (skeleton (if formula then q else p)) u) ∈
      Total.val (parameterConstructor R p q formula).left.hom
        (Nat.pair r (constantLift (if formula then q else p) r u)) := by
    apply (parameterConstructor_graph R p q formula r _ _).mpr
    exact ⟨hsource,by rw [constantUnlift_lift]⟩
  have hout : value ∈ Total.val (parameterConstructor R p q formula ≫ k).left.hom
      (Nat.pair r (constantLift (if formula then q else p) r u)) :=
    (Total.mem_val_comp _ _ _ _).mpr ⟨_,hc,hv⟩
  rw [← hk] at hout
  obtain ⟨m,hm,hvalue⟩ := (Total.mem_val_comp _ _ _ _).mp hout
  have hm' : Nat.pair (Nat.unpair m).1 (Nat.unpair m).2 ∈
      Total.val (rawAction R (uniformWordFamily R false p q) (uniformWordFamily R true p q)
        X Y f g (if formula then q else p)).left.hom
          (Nat.pair r (constantLift (if formula then q else p) r u)) := by
    simpa only [Nat.pair_unpair] using hm
  obtain ⟨hparameter,hchildren⟩ := (rawAction_graph R
    (uniformWordFamily R false p q) (uniformWordFamily R true p q) X Y f g
      (if formula then q else p) r (constantLift (if formula then q else p) r u)
        (Nat.unpair m).1 (Nat.unpair m).2).mp hm'
  refine ⟨(Nat.unpair m).2,
    (liftedAction_graph f g (if formula then q else p) r u (Nat.unpair m).2 hr hu).mp
      hchildren,?_⟩
  change value ∈ Total.val h.left.hom (Nat.pair r (Nat.unpair m).2)
  have hpair : Nat.pair r (Nat.unpair m).2=m := by
    rw [← hparameter,Nat.pair_unpair]
  rw [hpair]
  exact hvalue

/-- Every algebra morphism satisfies the guarded recursive root law. -/
theorem candidateRelation_rootLaw :
    UniformRootLaw p q (fun r => r∈R.obj.support)
      (operationRelation (algebraTermOperation B) (algebraFormulaOperation B))
      (candidateRelation f.f.1 f.f.2) := by
  intro formula r u value hu hv
  cases formula
  · exact constructor_factorization f.f.1 f.f.2 false (algebraTermOperation B) f.f.1
      (algebraHom_raw_term_constructor B f) r u value hu hv
  · exact constructor_factorization f.f.1 f.f.2 true (algebraFormulaOperation B) f.f.2
      (algebraHom_raw_formula_constructor B f) r u value hu hv

/-- Evaluator uniqueness now applies to the graph of every algebra morphism. -/
theorem algebraHom_candidate_fold_value (formula : Bool) (word : ℕ)
    (hw : word∈(uniformWords formula p q).support) (r x y : ℕ)
    (hx : candidateRelation f.f.1 f.f.2 formula r word x)
    (hy : foldRelation (algebraTermOperation B) (algebraFormulaOperation B) formula r word y) :
    x=y :=
  candidate_fold_value (algebraTermOperation B) (algebraFormulaOperation B)
    (candidateRelation f.f.1 f.f.2) (candidateRelation_rootLaw B f) formula word hw r x y hx hy

end CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
