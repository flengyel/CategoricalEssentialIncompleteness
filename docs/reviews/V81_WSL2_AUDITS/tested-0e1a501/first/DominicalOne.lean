import PCats.DominicalRecursion
import CategoricalEssentialIncompleteness.V46Comparison

open CategoryTheory CategoryTheory.PCategoryStruct CategoryTheory.CoprodStruct
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace FirstReaderDominical

inductive One | obj

instance : Category.{0} One where
  Hom _ _ := Unit
  id _ := ()
  comp _ _ := ()

instance (X Y : One) : Subsingleton (X ⟶ Y) := inferInstanceAs (Subsingleton Unit)

instance : Limits.HasZeroMorphisms One where
  zero _ _ := ⟨()⟩
  comp_zero := by intros; apply Subsingleton.elim
  zero_comp := by intros; apply Subsingleton.elim

instance : PCategoryStruct One where
  nearProd _ _ := .obj
  nearProd_map _ _ := ()
  diag _ := ()
  p0 _ _ := ()
  p1 _ _ := ()

theorem every_total {X Y : One} (f : X ⟶ Y) : DiPaolaHeller.IsTotal f :=
  fun _ _ => Subsingleton.elim _ _

instance : DiPaolaHeller.Dominical One := by
  constructor
  all_goals intros
  all_goals first
    | exact Subsingleton.elim _ _
    | exact every_total _
    | exact ⟨fun _ => Or.inl (Subsingleton.elim _ _), fun _ => Subsingleton.elim _ _⟩
    | exact ⟨(), ⟨every_total _, Subsingleton.elim _ _, Subsingleton.elim _ _⟩,
        fun _ _ _ _ => Subsingleton.elim _ _⟩

instance : PCategory One := (inferInstance : DiPaolaHeller.Dominical One).toPCategory

instance : RecursionCategory.Isotype One where
  iso _ _ := ⟨⟨(), (), Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩

instance : HasChoice One where
  exists_isSection := fun _ => ⟨(), Subsingleton.elim _ _, Subsingleton.elim _ _⟩

instance : CoprodStruct One where
  coprod _ _ := .obj
  coprod_map _ _ := ()
  codiag _ := ()
  i0 _ _ := ()
  i1 _ _ := ()

instance : HasCoproducts One := by constructor <;> intros <;> apply Subsingleton.elim

theorem coproduct_total {W X Y Z : One} (f : W ⟶ X) (g : Y ⟶ Z) :
    DiPaolaHeller.IsTotal (coprod_map f g) := every_total _

theorem every_iso {X Y : One} (f : X ⟶ Y) : IsIso f :=
  ⟨⟨(), Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩

instance : Distributive One where
  isIso_distribLeft := fun _ _ _ => every_iso _
  isIso_distribRight := fun _ _ _ => every_iso _

instance : RestrictionZero One := ⟨fun _ _ => Subsingleton.elim _ _⟩
instance : RestrictionCoproducts One :=
  ⟨fun _ _ => Subsingleton.elim _ _, fun _ _ => Subsingleton.elim _ _⟩

instance (X : One) : Subsingleton (Idem X) := ⟨fun _ _ => Idem.ext (Subsingleton.elim _ _)⟩

instance : BinaryJoins One where
  join _ _ := ⊤
  le_left := fun _ _ => le_top
  le_right := fun _ _ => le_top
  least := fun _ _ _ _ _ => le_of_eq (Subsingleton.elim _ _)

def evaluator : nearProd One.obj One.obj ⟶ coprod One.obj One.obj := ()

theorem evaluator_turing : DiPaolaHeller.IsTuringMorphism evaluator :=
  fun _ => ⟨(), every_total _, Subsingleton.elim _ _⟩

theorem identity_eq_zero : 𝟙 One.obj = (0 : One.obj ⟶ One.obj) := Subsingleton.elim _ _

theorem diagonal_pair_has_separator :
    let a := Idem.pull (diag One.obj ≫ evaluator) (summand0 One.obj One.obj)
    let b := Idem.pull (diag One.obj ≫ evaluator) (summand1 One.obj One.obj)
    a ⊓ b = ⊥ ∧ ∃ c c' : Idem One.obj, Complementary c c' ∧ a ≤ c ∧ b ≤ c' :=
  ⟨Subsingleton.elim _ _, ⊤, ⊤, ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩, le_top, le_top⟩

theorem diagonal_pair_separated :
    ¬ Inseparable (Idem.pull (diag One.obj ≫ evaluator) (summand0 One.obj One.obj))
      (Idem.pull (diag One.obj ≫ evaluator) (summand1 One.obj One.obj)) := by
  intro h
  exact h.no_separator diagonal_pair_has_separator.2

#print axioms evaluator_turing
#print axioms identity_eq_zero
#print axioms diagonal_pair_has_separator
#print axioms diagonal_pair_separated

end FirstReaderDominical
