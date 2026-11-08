import CategoricalEssentialIncompleteness.V46MillerSyntaxUniformFoldCommutation
import CategoricalEssentialIncompleteness.V46MillerSyntaxUniformHomLaws

/-! # The universal property on the original explicit parameter-word families

Constructor commutation comes from the actual polynomial action, and
uniqueness uses the root laws extracted from every algebra morphism.
Targets are arbitrary uniform slice families. The canonical constant-family
comparison is a separate constructed diagram, not an extra premise here.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
variable {P : Uniform.Family} {R : Total.TotalCategory P} {p q : SyntaxPolynomial (Total.TotalCategory P)}

def algebraFoldPair (B : Endofunctor.Algebra
    (SyntaxPolynomial.jointFunctor (p.withParameters R) (q.withParameters R))) :
    (parameterWordAlgebra R p q).a ⟶ B.a :=
  (uniformFold (algebraTermOperation B) (algebraFormulaOperation B) false,
    uniformFold (algebraTermOperation B) (algebraFormulaOperation B) true)

def parameterFoldHom (B : Endofunctor.Algebra
    (SyntaxPolynomial.jointFunctor (p.withParameters R) (q.withParameters R))) :
    parameterWordAlgebra R p q ⟶ B where
  f := algebraFoldPair B
  h := by
    apply Prod.ext
    · change (p.withParameters R).eval.map (algebraFoldPair B) ≫ B.str.1 =
        (parameterWordAlgebra R p q).str.1 ≫ (algebraFoldPair B).1
      apply (cancel_epi (comparison R (uniformWordFamily R false p q)
        (uniformWordFamily R true p q) p).hom).1
      calc
        (comparison R _ _ p).hom ≫ ((p.withParameters R).eval.map (algebraFoldPair B) ≫ B.str.1) =
            rawAction R _ _ B.a.1 B.a.2 (algebraFoldPair B).1 (algebraFoldPair B).2 p ≫
              algebraTermOperation B := by
          have h := rawAction_comparison R (uniformWordFamily R false p q)
            (uniformWordFamily R true p q) B.a.1 B.a.2
            (uniformFold (algebraTermOperation B) (algebraFormulaOperation B) false)
            (uniformFold (algebraTermOperation B) (algebraFormulaOperation B) true) p
          simpa only [algebraFoldPair,parameterWordAlgebra,algebraTermOperation,Category.assoc] using
            (congrArg (fun k => k ≫ B.str.1) h).symm
        _ = parameterConstructor R p q false ≫ (algebraFoldPair B).1 :=
          uniformFold_raw_commutes (algebraTermOperation B) (algebraFormulaOperation B) false
        _ = (comparison R _ _ p).hom ≫
            ((parameterWordAlgebra R p q).str.1 ≫ (algebraFoldPair B).1) := by
          simp only [parameterWordAlgebra,Category.assoc,Iso.hom_inv_id_assoc]
    · change (q.withParameters R).eval.map (algebraFoldPair B) ≫ B.str.2 =
        (parameterWordAlgebra R p q).str.2 ≫ (algebraFoldPair B).2
      apply (cancel_epi (comparison R (uniformWordFamily R false p q)
        (uniformWordFamily R true p q) q).hom).1
      calc
        (comparison R _ _ q).hom ≫ ((q.withParameters R).eval.map (algebraFoldPair B) ≫ B.str.2) =
            rawAction R _ _ B.a.1 B.a.2 (algebraFoldPair B).1 (algebraFoldPair B).2 q ≫
              algebraFormulaOperation B := by
          have h := rawAction_comparison R (uniformWordFamily R false p q)
            (uniformWordFamily R true p q) B.a.1 B.a.2
            (uniformFold (algebraTermOperation B) (algebraFormulaOperation B) false)
            (uniformFold (algebraTermOperation B) (algebraFormulaOperation B) true) q
          simpa only [algebraFoldPair,parameterWordAlgebra,algebraFormulaOperation,Category.assoc] using
            (congrArg (fun k => k ≫ B.str.2) h).symm
        _ = parameterConstructor R p q true ≫ (algebraFoldPair B).2 :=
          uniformFold_raw_commutes (algebraTermOperation B) (algebraFormulaOperation B) true
        _ = (comparison R _ _ q).hom ≫
            ((parameterWordAlgebra R p q).str.2 ≫ (algebraFoldPair B).2) := by
          simp only [parameterWordAlgebra,Category.assoc,Iso.hom_inv_id_assoc]

def candidateComponent {B : Endofunctor.Algebra
    (SyntaxPolynomial.jointFunctor (p.withParameters R) (q.withParameters R))}
    (f : parameterWordAlgebra R p q ⟶ B) : (formula : Bool) →
      uniformWordFamily R formula p q ⟶ (if formula then B.a.2 else B.a.1)
  | false => f.f.1
  | true => f.f.2

theorem candidateComponent_graph {B : Endofunctor.Algebra
    (SyntaxPolynomial.jointFunctor (p.withParameters R) (q.withParameters R))}
    (f : parameterWordAlgebra R p q ⟶ B) (formula : Bool) (r word value : ℕ) :
    candidateRelation f.f.1 f.f.2 formula r word value ↔
      value∈Total.val (candidateComponent f formula).left.hom (Nat.pair r word) := by
  cases formula <;> rfl

theorem candidateComponent_eq_fold {B : Endofunctor.Algebra
    (SyntaxPolynomial.jointFunctor (p.withParameters R) (q.withParameters R))}
    (f : parameterWordAlgebra R p q ⟶ B) (formula : Bool) :
    candidateComponent f formula =
      uniformFold (algebraTermOperation B) (algebraFormulaOperation B) formula := by
  apply Over.OverMorphism.ext
  apply WideSubcategory.hom_ext
  apply Total.val_ext_on_source
  intro n hn
  have hs : (Nat.unpair n).1∈R.obj.support ∧
      (Nat.unpair n).2∈(uniformWords formula p q).support := hn
  obtain ⟨x,hx⟩ := Part.dom_iff_mem.mp
    ((Total.total_iff (candidateComponent f formula).left.hom).mp
      (candidateComponent f formula).left.property n hn)
  obtain ⟨y,hy⟩ := Part.dom_iff_mem.mp
    ((Total.total_iff (uniformFold (algebraTermOperation B) (algebraFormulaOperation B) formula).left.hom).mp
      (uniformFold (algebraTermOperation B) (algebraFormulaOperation B) formula).left.property n hn)
  have hx' : candidateRelation f.f.1 f.f.2 formula (Nat.unpair n).1 (Nat.unpair n).2 x :=
    (candidateComponent_graph f formula _ _ _).mpr (by simpa only [Nat.pair_unpair] using hx)
  have hy' : foldRelation (algebraTermOperation B) (algebraFormulaOperation B)
      formula (Nat.unpair n).1 (Nat.unpair n).2 y := by
    simpa only [foldRelation,Nat.pair_unpair] using hy
  have he := candidate_fold_value (algebraTermOperation B) (algebraFormulaOperation B)
    (candidateRelation f.f.1 f.f.2) (candidateRelation_rootLaw B f)
    formula (Nat.unpair n).2 hs.2 (Nat.unpair n).1 x y hx' hy'
  subst y
  exact (Part.eq_some_iff.mpr hx).trans (Part.eq_some_iff.mpr hy).symm

theorem parameterFoldHom_unique (B : Endofunctor.Algebra
    (SyntaxPolynomial.jointFunctor (p.withParameters R) (q.withParameters R)))
    (f : parameterWordAlgebra R p q ⟶ B) : f=parameterFoldHom B := by
  apply Endofunctor.Algebra.Hom.ext
  apply Prod.ext
  · exact candidateComponent_eq_fold f false
  · exact candidateComponent_eq_fold f true

def explicitWordInitial (R : Total.TotalCategory P) (p q : SyntaxPolynomial (Total.TotalCategory P)) :
    IsInitial (parameterWordAlgebra R p q) :=
  IsInitial.ofUniqueHom (fun B => parameterFoldHom B) (fun B f => parameterFoldHom_unique B f)

end CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
