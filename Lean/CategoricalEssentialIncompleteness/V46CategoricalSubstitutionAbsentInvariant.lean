import CategoricalEssentialIncompleteness.V46CategoricalQuantifierAdmissibilityBranches

/-! Conditional equality and actual equalizer-subalgebra induction. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u v' u'
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]

namespace ConditionalInvariant

/-- Equality of the result with the original value whenever the Boolean test is false. -/
def Holds {X Y : D} (b : X ⟶ Two D) (original result : X ⟶ Y) : Prop :=
  Two.branch b original result = result

theorem fixed_of_false {X Y Z : D} {b : X ⟶ Two D} {original result : X ⟶ Y}
    (h : Holds b original result) (k : Z ⟶ X)
    (hb : k ≫ b = Two.constant Z false) : k ≫ result = k ≫ original := by
  have hh := congrArg (fun f => k ≫ f) h
  rw [Two.comp_branch _ _ _ k false hb] at hh
  exact hh.symm

theorem holds_of_false_fiber {X Y : D} (b : X ⟶ Two D) (original result : X ⟶ Y)
    (h : Two.fiberι b false ≫ result = Two.fiberι b false ≫ original) :
    Holds b original result := by
  apply Two.hom_ext b
  · rw [Two.fiberι_branch]
    exact h.symm
  · exact Two.fiberι_branch b original result true

theorem holds_iff_false_fiber {X Y : D} (b : X ⟶ Two D) (original result : X ⟶ Y) :
    Holds b original result ↔
      Two.fiberι b false ≫ result = Two.fiberι b false ≫ original :=
  ⟨fun h => fixed_of_false h _ (Two.fiberι_comp b false),
    holds_of_false_fiber b original result⟩

theorem precomp {X Y Z : D} {b : X ⟶ Two D} {original result : X ⟶ Y}
    (h : Holds b original result) (k : Z ⟶ X) :
    Holds (k ≫ b) (k ≫ original) (k ≫ result) := by
  have hh := congrArg (fun f => k ≫ f) h
  simpa only [Holds, branch_natural] using hh

end ConditionalInvariant

namespace DecidableVariables

variable {V : D} (E : DecidableVariables V)

theorem test_reverse {X : D} (x y : X ⟶ V) :
    prod.lift x y ≫ E.test = prod.lift y x ≫ E.test := by
  have hle (x y : X ⟶ V) : prod.lift x y ≫ E.test ≤ prod.lift y x ≫ E.test := by
    let b := prod.lift x y ≫ E.test
    let k := Two.fiberι b true
    apply boolean_le_of_true b (prod.lift y x ≫ E.test)
    have he : k ≫ x = k ≫ y := (E.test_true_iff _ _).mp (by
      simpa only [b, prod.comp_lift_assoc] using Two.fiberι_comp b true)
    simpa only [prod.comp_lift_assoc] using (E.test_true_iff (k ≫ y) (k ≫ x)).mpr he.symm
  exact le_antisymm (hle x y) (hle y x)

end DecidableVariables

namespace AlgebraInvariant

variable {C : Type u'} [Category.{v'} C] [HasEqualizers C]
variable {F : C ⥤ C}

/-- Construct the actual subalgebra equalizing two morphisms whenever its
constructor images equalize them. -/
def equalizerAlgebra (B : Endofunctor.Algebra F) {Z : C} (f g : B.a ⟶ Z)
    (closed : ∀ {X : C} (m : X ⟶ B.a), m ≫ f = m ≫ g →
      (F.map m ≫ B.str) ≫ f = (F.map m ≫ B.str) ≫ g) :
    Endofunctor.Algebra F where
  a := equalizer f g
  str := equalizer.lift (F.map (equalizer.ι f g) ≫ B.str)
    (closed (equalizer.ι f g) (equalizer.condition f g))

def equalizerInclusion (B : Endofunctor.Algebra F) {Z : C} (f g : B.a ⟶ Z)
    (closed : ∀ {X : C} (m : X ⟶ B.a), m ≫ f = m ≫ g →
      (F.map m ≫ B.str) ≫ f = (F.map m ≫ B.str) ≫ g) :
    equalizerAlgebra B f g closed ⟶ B where
  f := equalizer.ι f g
  h := (equalizer.lift_ι _ _).symm

/-- Initiality factors the actual algebra fold through the constructed
closed equalizer subalgebra. -/
theorem fold_equalizes (A B : Endofunctor.Algebra F) (hA : IsInitial A)
    {Z : C} (f g : B.a ⟶ Z)
    (closed : ∀ {X : C} (m : X ⟶ B.a), m ≫ f = m ≫ g →
      (F.map m ≫ B.str) ≫ f = (F.map m ≫ B.str) ≫ g) :
    (hA.to B).f ≫ f = (hA.to B).f ≫ g := by
  let N := equalizerAlgebra B f g closed
  let j := equalizerInclusion B f g closed
  have he : (hA.to N) ≫ j = hA.to B := hA.hom_ext _ _
  have hf : (hA.to N).f ≫ equalizer.ι f g = (hA.to B).f :=
    congrArg Endofunctor.Algebra.Hom.f he
  rw [← hf, Category.assoc, Category.assoc, equalizer.condition]

end AlgebraInvariant
end CategoricalEssentialIncompleteness.V46
