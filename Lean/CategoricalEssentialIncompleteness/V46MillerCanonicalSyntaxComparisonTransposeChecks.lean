import CategoricalEssentialIncompleteness.V46MillerCanonicalSyntaxComparisonTranspose
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.Miller.CanonicalPresentation
universe v₁ v₂ u₁ u₂
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
section BareEquivalence
variable (E : C ≌ D)
example {X Y : C} {X' Y' : D} (i : E.functor.obj X ≅ X') (j : E.functor.obj Y ≅ Y')
    (f : X ⟶ Y) (g : X' ⟶ Y') (h : E.functor.map f≫j.hom=i.hom≫g) :
    E.inverse.map g≫(transposeIso E j).hom=(transposeIso E i).hom≫f :=
  transpose_square E i j f g h
example (X : C) : transposeIso E (Iso.refl (E.functor.obj X))=(E.unitIso.app X).symm :=
  transpose_refl E X
example (X : C) : transposeIso E.symm (E.unitIso.app X).symm=Iso.refl (E.functor.obj X) :=
  transpose_unit_inverse E X
end BareEquivalence

variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
variable (E : C ≌ D) (V : C) (L : StableListAlgebra V)
local notation "M" => SyntacticLists.Transport.mappedStableListAlgebra E V (E.functor.obj V) (Iso.refl _) L
example {X Y : C} {X' Y' : D} (i : E.functor.obj X ≅ X') (j : E.functor.obj Y ≅ Y') :
    transposeIso E (SyntaxOptionTransport.productIso E i j)=
      SyntaxOptionTransport.productIso E.symm (transposeIso E i) (transposeIso E j) :=
  transpose_product E i j
example : transposeIso E (DecidableVariables.Transport.booleanIso E)=
    DecidableVariables.Transport.booleanIso E.symm := transpose_boolean E
example {X : C} {X' : D} (i : E.functor.obj X ≅ X') :
    transposeIso E (SyntaxOptionTransport.optionIso E i)=
      SyntaxOptionTransport.optionIso E.symm (transposeIso E i) := transpose_option E i
example : E.inverse.map (M).algebra.nil ≫ (E.unitIso.app L.algebra.carrier).inv =
    terminalComparison E.inverse ≫ L.algebra.nil := reverseList_nil E V L
example : E.inverse.map (M).append ≫ (E.unitIso.app L.algebra.carrier).inv =
    (SyntaxOptionTransport.productIso E.symm (E.unitIso.app L.algebra.carrier).symm
      (E.unitIso.app L.algebra.carrier).symm).hom ≫ L.append := reverseList_append E V L
example : E.inverse.map (M).singleton≫(E.unitIso.app L.algebra.carrier).inv=
    (E.unitIso.app V).inv≫L.singleton := reverseList_singleton E V L
example (S : DecidableVariables V) (T : DecidableVariables (E.functor.obj V)) :
    E.inverse.map ((M).deletion T)≫(E.unitIso.app L.algebra.carrier).inv=
      (SyntaxOptionTransport.productIso E.symm (E.unitIso.app V).symm
        (E.unitIso.app L.algebra.carrier).symm).hom≫L.deletion S :=
  reverseList_deletion E V L S T
example (S : DecidableVariables V) (T : DecidableVariables (E.functor.obj V)) :
    E.inverse.map ((M).membership T)≫(DecidableVariables.Transport.booleanIso E.symm).hom=
      (SyntaxOptionTransport.productIso E.symm (E.unitIso.app V).symm
        (E.unitIso.app L.algebra.carrier).symm).hom≫L.membership S :=
  reverseList_membership E V L S T
end CategoricalEssentialIncompleteness.V46.Miller.CanonicalPresentation
