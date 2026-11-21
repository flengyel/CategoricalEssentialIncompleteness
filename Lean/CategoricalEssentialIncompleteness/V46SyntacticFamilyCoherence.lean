/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.SyntacticFamilyExtension
public import Mathlib.CategoryTheory.Whiskering

/-! # Identity, composition and square coherence for theory-indexed families -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FailureOfComposition.TypedProgramCategory FailureOfComposition.UniformIndexQuotient
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.LocalConnectedness.SyntacticModel
open CategoricalEssentialIncompleteness.LocalConnectedness.PartialFunctionFamilies

namespace CategoricalEssentialIncompleteness.V46.SyntacticFamilyCoherence

section Identity

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

/-- The quotient at an identity theory extension is the identity on every program class,
independently of its chosen representative. -/
theorem programMap_id (q : ProgramQuotient T) : SyntacticExtension.programMap T T q = q := by
  induction q using Quotient.inductionOn with
  | _ q => rfl

theorem quotient_id : SyntacticExtension.functor T T = 𝟭 (CodedProgramCategory T) := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro Q R f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  apply CodedHom.ext
  exact programMap_id T f.val

omit [𝗣𝗔 ⪯ T] in
/-- Restriction at an identity inclusion keeps the entire arithmetic
structure, including its possibly nonstandard numeral interpretation. -/
theorem modelIndex_id (s : ModelIndex T) : restrictModelIndex T T s = s := by
  apply Subtype.ext
  rfl

omit [𝗣𝗔 ⪯ T] in
theorem projection_id : familyProjection T T = 𝟭 (Family.{0} (ModelIndex T)) := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro X Y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  funext s
  rfl

end Identity

section Extension

variable (T T' : ArithmeticTheory) [𝗣𝗔 ⪯ T] [𝗣𝗔 ⪯ T'] [T ⪯ T']

/-- The commuting family square with explicit identity comparison maps
on its common interpreted object families. -/
def square : SyntacticExtension.functor T T' ⋙ familyFunctor T' ≅
    familyFunctor T ⋙ familyProjection T T' :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro Q R f
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    funext s
    let := s.val
    have := s.property
    exact model_extension_map T T' f)

@[simp] theorem square_hom_app (Q : CodedProgramCategory T) :
    (square T T').hom.app Q = 𝟙 ((familyFunctor T').obj
      ((SyntacticExtension.functor T T').obj Q)) := rfl

@[simp] theorem square_inv_app (Q : CodedProgramCategory T) :
    (square T T').inv.app Q = 𝟙 ((familyFunctor T').obj
      ((SyntacticExtension.functor T T').obj Q)) := rfl

theorem square_naturality {Q R : CodedProgramCategory T} (f : Q ⟶ R) :
    (familyFunctor T').map ((SyntacticExtension.functor T T').map f) ≫
        (square T T').hom.app R =
      (square T T').hom.app Q ≫ (familyProjection T T').map ((familyFunctor T).map f) :=
  (square T T').hom.naturality f

end Extension

section Composition

variable (T T' T'' : ArithmeticTheory) [𝗣𝗔 ⪯ T] [𝗣𝗔 ⪯ T'] [𝗣𝗔 ⪯ T'']
variable [T ⪯ T'] [T' ⪯ T'']

/-- The direct inclusion is derived from the two given inclusions; it is
not an additional hypothesis in the composition statements. -/
theorem compositeInclusion (U U' U'' : ArithmeticTheory) [U ⪯ U'] [U' ⪯ U''] :
    U ⪯ U'' := WeakerThan.trans (inferInstance : U ⪯ U') (inferInstance : U' ⪯ U'')

theorem programMap_comp (q : ProgramQuotient T) :
    have := compositeInclusion T T' T''
    SyntacticExtension.programMap T' T'' (SyntacticExtension.programMap T T' q) =
      SyntacticExtension.programMap T T'' q := by
  have := compositeInclusion T T' T''
  induction q using Quotient.inductionOn with
  | _ q => rfl

theorem quotient_comp :
    have := compositeInclusion T T' T''
    SyntacticExtension.functor T T' ⋙ SyntacticExtension.functor T' T'' =
      SyntacticExtension.functor T T'' := by
  have := compositeInclusion T T' T''
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro Q R f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  apply CodedHom.ext
  exact programMap_comp T T' T'' f.val

omit [𝗣𝗔 ⪯ T] [𝗣𝗔 ⪯ T'] [𝗣𝗔 ⪯ T''] in
theorem modelIndex_comp (s : ModelIndex T'') :
    have := compositeInclusion T T' T''
    restrictModelIndex T T' (restrictModelIndex T' T'' s) = restrictModelIndex T T'' s := by
  have := compositeInclusion T T' T''
  apply Subtype.ext
  rfl

omit [𝗣𝗔 ⪯ T] [𝗣𝗔 ⪯ T'] [𝗣𝗔 ⪯ T''] in
theorem projection_comp :
    have := compositeInclusion T T' T''
    familyProjection T T' ⋙ familyProjection T' T'' = familyProjection T T'' := by
  have := compositeInclusion T T' T''
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro X Y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  funext s
  rfl

/-- Paste the two extension squares, retaining the source and target parentheses so that
the comparison has its full typed meaning. -/
def pastedSquare :
    (SyntacticExtension.functor T T' ⋙ SyntacticExtension.functor T' T'') ⋙
        familyFunctor T'' ≅
      familyFunctor T ⋙ (familyProjection T T' ⋙ familyProjection T' T'') :=
  Functor.associator (SyntacticExtension.functor T T')
      (SyntacticExtension.functor T' T'') (familyFunctor T'') ≪≫
    Functor.isoWhiskerLeft (SyntacticExtension.functor T T') (square T' T'') ≪≫
    (Functor.associator (SyntacticExtension.functor T T')
      (familyFunctor T') (familyProjection T' T'')).symm ≪≫
    Functor.isoWhiskerRight (square T T') (familyProjection T' T'') ≪≫
    Functor.associator (familyFunctor T) (familyProjection T T') (familyProjection T' T'')

/-- Compare the same endpoints by the direct extension, using the proved
identity of the two-stage quotient and family projection functors. -/
def directSquare :
    (SyntacticExtension.functor T T' ⋙ SyntacticExtension.functor T' T'') ⋙
        familyFunctor T'' ≅
      familyFunctor T ⋙ (familyProjection T T' ⋙ familyProjection T' T'') := by
  have := compositeInclusion T T' T''
  exact Functor.isoWhiskerRight (eqToIso (quotient_comp T T' T'')) (familyFunctor T'') ≪≫
    square T T'' ≪≫
    Functor.isoWhiskerLeft (familyFunctor T) (eqToIso (projection_comp T T' T'')).symm

@[simp] theorem pastedSquare_hom_app (Q : CodedProgramCategory T) :
    (pastedSquare T T' T'').hom.app Q = 𝟙 _ := by
  simp [pastedSquare]

@[simp] theorem directSquare_hom_app (Q : CodedProgramCategory T) :
    (directSquare T T' T'').hom.app Q = 𝟙 _ := by
  simp [directSquare]
  rfl

/-- The direct square and the pasted square agree as natural isomorphisms, including their
maps at every model coordinate. -/
theorem square_comp_coherence : pastedSquare T T' T'' = directSquare T T' T'' := by
  apply Iso.ext
  apply NatTrans.ext
  funext Q
  simp

end Composition

section UnitCoherence

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

def unitSquare : SyntacticExtension.functor T T ⋙ familyFunctor T ≅
    familyFunctor T ⋙ familyProjection T T :=
  Functor.isoWhiskerRight (eqToIso (quotient_id T)) (familyFunctor T) ≪≫
    Functor.leftUnitor (familyFunctor T) ≪≫
    (Functor.rightUnitor (familyFunctor T)).symm ≪≫
    Functor.isoWhiskerLeft (familyFunctor T) (eqToIso (projection_id T)).symm

/-- The identity extension square is the usual unitor comparison. -/
theorem square_unit_coherence : square T T = unitSquare T := by
  apply Iso.ext
  apply NatTrans.ext
  funext Q
  simp [unitSquare]
  rfl

end UnitCoherence

end CategoricalEssentialIncompleteness.V46.SyntacticFamilyCoherence
