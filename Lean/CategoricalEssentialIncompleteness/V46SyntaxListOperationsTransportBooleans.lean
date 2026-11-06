import CategoricalEssentialIncompleteness.V46SyntaxListOperationsTransport
import CategoricalEssentialIncompleteness.V46SyntaxBooleanTransport

/-! Boolean truth tables needed by the actual transported list and
substitution algebras. The proofs use actual coproduct fibers. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂ v₃ u₃
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.SyntaxOperationsTransport
open DecidableVariables.Transport

section Fibers
variable {K : Type u₃} [Category.{v₃} K] [Regular K] [FinitaryExtensive K]

theorem transport_branch_postcomp {X Y Z : K} (χ : X ⟶ Two K)
    (f g : X ⟶ Y) (h : Y ⟶ Z) :
    Two.branch χ f g ≫ h = Two.branch χ (f ≫ h) (g ≫ h) := by
  have hb (b : Bool) : Two.fiberι χ b ≫ (Two.branch χ f g ≫ h) =
      Two.fiberι χ b ≫ Two.branch χ (f ≫ h) (g ≫ h) := by
    rw [← Category.assoc,Two.fiberι_branch,Two.fiberι_branch]
    cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true,Category.assoc]
  exact Two.hom_ext χ (hb false) (hb true)

theorem boolean_unary_as_branch {X : K} (op : Bool → Bool) (f : X ⟶ Two K) :
    Two.unary op f = Two.branch f (Two.constant X (op false)) (Two.constant X (op true)) := by
  have hb (b : Bool) : Two.fiberι f b ≫ Two.unary op f =
      Two.fiberι f b ≫ Two.branch f (Two.constant X (op false)) (Two.constant X (op true)) := by
    rw [Two.comp_unary,Two.fiberι_comp,Two.unary_constant,Two.fiberι_branch]
    cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true,Two.comp_constant]
  exact Two.hom_ext f (hb false) (hb true)

theorem boolean_binary_as_branch {X : K} (op : Bool → Bool → Bool) (f g : X ⟶ Two K) :
    Two.binary op f g = Two.branch f (Two.unary (op false) g) (Two.unary (op true) g) := by
  unfold Two.binary Two.binaryArrow
  rw [branch_precomp]
  simp only [prod.lift_fst,Two.comp_unary,prod.lift_snd]

end Fibers

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
variable (E : C ≌ D)

/-- Every unary Boolean truth table commutes with the actual Boolean
comparison, including complementation. -/
theorem map_boolean_unary {X : C} (op : Bool → Bool) (f : X ⟶ Two C) :
    E.functor.map (Two.unary op f) ≫ (booleanIso E).hom =
      Two.unary op (E.functor.map f ≫ (booleanIso E).hom) := by
  rw [boolean_unary_as_branch,map_branch E,transport_branch_postcomp,
    map_constant E X (op false),map_constant E X (op true)]
  exact (boolean_unary_as_branch op (E.functor.map f ≫ (booleanIso E).hom)).symm

/-- Every binary Boolean truth table commutes with the actual Boolean
comparison; no chosen codes for either truth point are used. -/
theorem map_boolean_binary {X : C} (op : Bool → Bool → Bool) (f g : X ⟶ Two C) :
    E.functor.map (Two.binary op f g) ≫ (booleanIso E).hom =
      Two.binary op (E.functor.map f ≫ (booleanIso E).hom)
        (E.functor.map g ≫ (booleanIso E).hom) := by
  rw [boolean_binary_as_branch,map_branch E,transport_branch_postcomp,
    map_boolean_unary E (op false) g,map_boolean_unary E (op true) g]
  exact (boolean_binary_as_branch op (E.functor.map f ≫ (booleanIso E).hom)
    (E.functor.map g ≫ (booleanIso E).hom)).symm

/-- The target may use any proved internal decidable equality. Its
diagonal pullback forces agreement with the transported source test. -/
theorem map_decidable_test {V : C} (S : DecidableVariables V)
    (W : D) (e : E.functor.obj V ≅ W) (T : DecidableVariables W) :
    E.functor.map S.test ≫ (booleanIso E).hom =
      (productIso E V W e).hom ≫ T.test := by
  rw [← equality_test_unique (mapped E S W e) T]
  change E.functor.map S.test ≫ (booleanIso E).hom =
    (productIso E V W e).hom ≫
      ((productIso E V W e).inv ≫ E.functor.map S.test ≫ (booleanIso E).hom)
  simp only [Iso.hom_inv_id_assoc]

end CategoricalEssentialIncompleteness.V46.SyntaxOperationsTransport
