import CategoricalEssentialIncompleteness.V46MillerSyntaxUniformAlgebra
import CategoricalEssentialIncompleteness.V46MillerSyntaxRawComparison
import CategoricalEssentialIncompleteness.V46MillerSyntaxRawConstants

/-! # Literal constructors on the explicit parameter families

A recursive child in a constant family is a pair of the external parameter
and its word. The input chart removes that parameter at each recursive leaf
before constructing the new word. Coefficient values and ordered children
remain unchanged. This constructs an algebra, without assuming initiality
or its comparison with the canonical parameter algebra.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
open SyntacticSyntax SyntacticSyntax.Coding
variable {P : Uniform.Family}
variable (R : Total.TotalCategory P) (p q : SyntaxPolynomial (Total.TotalCategory P))

def parameterConstructorCode (formula : Bool) (n : ℕ) : ℕ :=
  Nat.pair (Nat.unpair n).1
    (constructor formula (skeleton (if formula then q else p))
      (constantUnlift (if formula then q else p) (Nat.unpair n).2))

theorem parameterConstructorCode_primrec (formula : Bool) :
    Primrec (parameterConstructorCode p q formula) :=
  Primrec₂.natPair.comp (Primrec.fst.comp Primrec.unpair)
    ((NatVectors.constructor_primrec formula (skeleton (if formula then q else p))).comp
      ((constantUnlift_primrec (if formula then q else p)).comp
        (Primrec.snd.comp Primrec.unpair)))

theorem wordFamily_constant (formula : Bool) :
    uniformWordFamily R formula p q = constantObject R (wordObject formula p q) := rfl

theorem parameterConstructorCode_supported (formula : Bool) (n : ℕ)
    (hn : n ∈ (object R (uniformWordFamily R false p q)
      (uniformWordFamily R true p q) (if formula then q else p)).left.obj.support) :
    parameterConstructorCode p q formula n ∈ (uniformWordFamily R formula p q).left.obj.support := by
  have hu : fiber R (constantObject R (wordObject false p q))
      (constantObject R (wordObject true p q)) (if formula then q else p) (Nat.unpair n) := hn
  obtain ⟨hr,hw⟩ := constantUnlift_supported R (wordObject false p q)
    (wordObject true p q) (if formula then q else p)
    (r:=(Nat.unpair n).1) (u:=(Nat.unpair n).2) hu
  have hc := uniformWords_constructor p q formula hw
  exact (show (Nat.unpair (parameterConstructorCode p q formula n)).1 ∈ R.obj.support ∧
      (Nat.unpair (parameterConstructorCode p q formula n)).2 ∈
        (uniformWords formula p q).support from by
    simpa only [parameterConstructorCode,Nat.unpair_pair] using And.intro hr hc)

def parameterConstructorLeft (formula : Bool) :
    (object R (uniformWordFamily R false p q) (uniformWordFamily R true p q)
      (if formula then q else p)).left ⟶ (uniformWordFamily R formula p q).left :=
  ⟨Total.totalFromFunction (parameterConstructorCode p q formula)
    (parameterConstructorCode_primrec p q formula).to_comp
    (parameterConstructorCode_supported R p q formula),Total.totalFromFunction_total _ _ _⟩

theorem parameterConstructor_parameter (formula : Bool) :
    parameterConstructorLeft R p q formula ≫ (uniformWordFamily R formula p q).hom =
      (object R (uniformWordFamily R false p q) (uniformWordFamily R true p q)
        (if formula then q else p)).hom := by
  apply WideSubcategory.hom_ext
  apply Total.val_ext_on_source
  intro n hn
  have he : Total.val (parameterConstructorLeft R p q formula).hom n =
      Part.some (parameterConstructorCode p q formula n) :=
    Part.eq_some_iff.mpr ((Total.mem_totalFromFunction (parameterConstructorCode p q formula)
      (parameterConstructorCode_primrec p q formula).to_comp
      (parameterConstructorCode_supported R p q formula) n _).mpr ⟨hn,rfl⟩)
  have ht : Total.val (uniformWordFamily R formula p q).hom.hom
      (parameterConstructorCode p q formula n) = Part.some (Nat.unpair n).1 :=
    Part.eq_some_iff.mpr ((Total.mem_partialFst _ _ _ _).mpr
      ⟨parameterConstructorCode_supported R p q formula n hn,by
        simp only [parameterConstructorCode,Nat.unpair_pair]⟩)
  have hs : Total.val (object R (uniformWordFamily R false p q)
      (uniformWordFamily R true p q) (if formula then q else p)).hom.hom n =
      Part.some (Nat.unpair n).1 :=
    Part.eq_some_iff.mpr ((projection_graph _ _ _ _ n _).mpr ⟨hn,rfl⟩)
  change Total.val ((parameterConstructorLeft R p q formula).hom ≫
    (uniformWordFamily R formula p q).hom.hom) n =
      Total.val (object R (uniformWordFamily R false p q)
        (uniformWordFamily R true p q) (if formula then q else p)).hom.hom n
  rw [Total.val_comp,he,Part.bind_some,ht,hs]

def parameterConstructor (formula : Bool) :
    object R (uniformWordFamily R false p q) (uniformWordFamily R true p q)
      (if formula then q else p) ⟶ uniformWordFamily R formula p q :=
  Over.homMk (parameterConstructorLeft R p q formula)
    (parameterConstructor_parameter R p q formula)

theorem parameterConstructor_graph (formula : Bool) (r u value : ℕ) :
    value ∈ Total.val (parameterConstructor R p q formula).left.hom (Nat.pair r u) ↔
      fiber R (uniformWordFamily R false p q) (uniformWordFamily R true p q)
        (if formula then q else p) (r,u) ∧
      value = Nat.pair r (constructor formula (skeleton (if formula then q else p))
        (constantUnlift (if formula then q else p) u)) := by
  have h := Total.mem_totalFromFunction (parameterConstructorCode p q formula)
    (parameterConstructorCode_primrec p q formula).to_comp
    (parameterConstructorCode_supported R p q formula) (Nat.pair r u) value
  change (value∈Total.val (parameterConstructor R p q formula).left.hom (Nat.pair r u) ↔
    fiber R (uniformWordFamily R false p q) (uniformWordFamily R true p q)
      (if formula then q else p) (Nat.unpair (Nat.pair r u)) ∧
    value=parameterConstructorCode p q formula (Nat.pair r u)) at h
  simpa only [parameterConstructorCode,Nat.unpair_pair] using h

def parameterWordAlgebra : Endofunctor.Algebra
    (SyntaxPolynomial.jointFunctor (p.withParameters R) (q.withParameters R)) where
  a := (uniformWordFamily R false p q,uniformWordFamily R true p q)
  str := ((comparison R _ _ p).inv ≫ parameterConstructor R p q false,
    (comparison R _ _ q).inv ≫ parameterConstructor R p q true)

theorem parameterWordAlgebra_term_constructor :
    (comparison R _ _ p).hom ≫ (parameterWordAlgebra R p q).str.1 =
      parameterConstructor R p q false := by
  simp only [parameterWordAlgebra,Iso.hom_inv_id_assoc]

theorem parameterWordAlgebra_formula_constructor :
    (comparison R _ _ q).hom ≫ (parameterWordAlgebra R p q).str.2 =
      parameterConstructor R p q true := by
  simp only [parameterWordAlgebra,Iso.hom_inv_id_assoc]

end CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
