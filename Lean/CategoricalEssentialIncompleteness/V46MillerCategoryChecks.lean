import CategoricalEssentialIncompleteness.V46MillerCategory
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.Uniform
variable {z : Family}
attribute [instance 2000] nativeRestriction

example : Category (Object z) := inferInstance
example : RestrictionCategory (Object z) := nativeRestriction
example : HasZeroMorphisms (Object z) := inferInstance
example : RestrictionZero (Object z) := inferInstance
example : Ranges (Object z) := inferInstance
example : (inclusion z).Faithful := inferInstance
example {X Y : Object z} (f : X ⟶ Y) :
    ∃ e : ℕ,∀ p ∈ z.oracles,∀ x y,
      y ∈ f.val x ↔ Y.type.toNat y ∈ OracleProgram.numberedEval e p (X.type.toNat x) :=
  f.represented
example {X Y : Object z} (f : X ⟶ Y) :
    (rst f).val = rst (C := PartialFunctions.Pfn) f.val := restriction_val f
example {X Y : Object z} (f : X ⟶ Y) (x y : carrier z Y) :
    y ∈ (Ranges.range f).hom.val x ↔ (∃ a,x ∈ f.val a) ∧ y = x := mem_range f x y
example {X Y : Object z} (f : X ⟶ Y) : isTotal f ↔ ∀ x,(f.val x).Dom := total_iff f
example (X : Object z) : X ≅ N z := codeIso X
example (X : Object z) : (codeIso X).hom.val = fun x => Part.some (X.type.toNat x) := rfl
example (X : Object z) : (codeIso X).inv.val = fun n => Part.some (X.type.fromNat n) := rfl
example : RecursionCategory.Isotype (Object z) := inferInstance
end CategoricalEssentialIncompleteness.V46.Miller.Uniform
