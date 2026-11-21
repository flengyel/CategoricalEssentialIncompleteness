/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalNamedLiteralOperations
public import CategoricalEssentialIncompleteness.V46NumericalNamedLiteralConstructorValues
public import CategoricalEssentialIncompleteness.V46NumericalNamedLiteralListValues
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxPlain

/-! # Constructor-preserving initial algebras on numerical words -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalNamed

section Conjugation
variable {C : Type u} [Category.{v} C]

def algebraOnIso (F : C ⥤ C) (A : Endofunctor.Algebra F) {X : C} (i : A.a ≅ X) :
    Endofunctor.Algebra F where
  a := X
  str := F.map i.inv ≫ A.str ≫ i.hom

def algebraOnIsoComparison (F : C ⥤ C) (A : Endofunctor.Algebra F)
    {X : C} (i : A.a ≅ X) : A ≅ algebraOnIso F A i := by
  refine Endofunctor.Algebra.isoMk i ?_
  change F.map i.hom ≫ (F.map i.inv ≫ A.str ≫ i.hom) = A.str ≫ i.hom
  rw [← Category.assoc, ← F.map_comp, i.hom_inv_id, F.map_id, Category.id_comp]

theorem operation_precompose_square {A B C₀ D X : C}
    (f : A ⟶ B) (j : B ≅ D) (k : A ⟶ C₀) (g : C₀ ⟶ D)
    (hf : f ≫ j.hom = k ≫ g) (u : X ⟶ A) :
    (u ≫ f ≫ j.hom) ≫ (Iso.refl D).hom = (u ≫ k) ≫ g := by
  simpa only [Iso.refl_hom, Category.comp_id, Category.assoc] using
    congrArg (fun q => u ≫ q) hf

end Conjugation

section Lists
variable {C : Type u} [Category.{v} C] [HasFiniteLimits C] [HasFiniteCoproducts C]
variable {V : C}

def listOnIso (L : ListAlgebra V) {X : C} (i : L.carrier ≅ X) : ListAlgebra V where
  carrier := X
  nil := L.nil ≫ i.hom
  cons := prod.map (𝟙 V) i.inv ≫ L.cons ≫ i.hom

def listOnIsoComparison (L : ListAlgebra V) {X : C} (i : L.carrier ≅ X) :
    L.asAlgebra ≅ (listOnIso L i).asAlgebra := by
  refine SyntacticLists.Transport.constructorsIso L (listOnIso L i) i rfl ?_
  simp only [listOnIso, prod.map_map_assoc, Category.id_comp,
    i.hom_inv_id, prod.map_id_id]

/-- The constructor equations themselves remain equations in every slice. -/
def listParameterIso (L R : ListAlgebra V) (i : L.carrier ≅ R.carrier)
    (hn : L.nil ≫ i.hom = R.nil)
    (hc : L.cons ≫ i.hom = prod.map (𝟙 V) i.hom ≫ R.cons) (P : C) :
    (L.withParameters P).asAlgebra ≅ (R.withParameters P).asAlgebra := by
  refine SyntacticLists.Transport.constructorsIso (L.withParameters P) (R.withParameters P)
    ((constantFamilyFunctor P).mapIso i) ?_ ?_
  · apply Over.OverMorphism.ext
    apply prod.hom_ext
    · exact (Over.w ((L.withParameters P).nil ≫
        ((constantFamilyFunctor P).mapIso i).hom)).trans
        (Over.w (R.withParameters P).nil).symm
    · change (prod.lift (⊤_ (Over P)).hom
        (terminal.from (⊤_ (Over P)).left ≫ L.nil) ≫ prod.map (𝟙 P) i.hom) ≫ prod.snd =
          prod.lift (⊤_ (Over P)).hom
            (terminal.from (⊤_ (Over P)).left ≫ R.nil) ≫ prod.snd
      simp only [Category.assoc, prod.map_snd, prod.lift_snd]
      rw [← Category.assoc, prod.lift_snd, Category.assoc, hn]
  · let U := constantFamily P V ⨯ constantFamily P L.carrier
    let Z := constantFamily P V ⨯ constantFamily P R.carrier
    let rS : U.left ⟶ V ⨯ L.carrier := prod.lift
      ((prod.fst : U ⟶ constantFamily P V).left ≫ prod.snd)
      ((prod.snd : U ⟶ constantFamily P L.carrier).left ≫ prod.snd)
    let rR : Z.left ⟶ V ⨯ R.carrier := prod.lift
      ((prod.fst : Z ⟶ constantFamily P V).left ≫ prod.snd)
      ((prod.snd : Z ⟶ constantFamily P R.carrier).left ≫ prod.snd)
    let m : U ⟶ Z := prod.map (𝟙 (constantFamily P V))
      ((constantFamilyFunctor P).mapIso i).hom
    have hf : m.left ≫ (prod.fst : Z ⟶ constantFamily P V).left =
        (prod.fst : U ⟶ constantFamily P V).left := by
      have h := congrArg Over.Hom.left
        (prod.map_fst (𝟙 (constantFamily P V)) ((constantFamilyFunctor P).mapIso i).hom)
      change m.left ≫ (prod.fst : Z ⟶ constantFamily P V).left =
        (prod.fst : U ⟶ constantFamily P V).left ≫ 𝟙 _ at h
      exact h.trans (Category.comp_id _)
    have hs : m.left ≫ (prod.snd : Z ⟶ constantFamily P R.carrier).left =
        (prod.snd : U ⟶ constantFamily P L.carrier).left ≫ prod.map (𝟙 P) i.hom := by
      have h := congrArg Over.Hom.left
        (prod.map_snd (𝟙 (constantFamily P V)) ((constantFamilyFunctor P).mapIso i).hom)
      change m.left ≫ (prod.snd : Z ⟶ constantFamily P R.carrier).left =
        (prod.snd : U ⟶ constantFamily P L.carrier).left ≫ prod.map (𝟙 P) i.hom at h
      exact h
    have hr : m.left ≫ rR = rS ≫ prod.map (𝟙 V) i.hom := by
      apply prod.hom_ext
      · simp only [Category.assoc, rR, rS, prod.lift_fst, prod.map_fst, Category.comp_id]
        rw [← Category.assoc, hf]
      · simp only [Category.assoc, rR, rS, prod.lift_snd, prod.map_snd]
        rw [← Category.assoc, hs]
        simp only [Category.assoc, prod.map_snd, prod.lift_snd_assoc]
    apply Over.OverMorphism.ext
    apply prod.hom_ext
    · exact (Over.w ((L.withParameters P).cons ≫
        ((constantFamilyFunctor P).mapIso i).hom)).trans
        (Over.w (m ≫ (R.withParameters P).cons)).symm
    · change (prod.lift _ (rS ≫ L.cons) ≫ prod.map (𝟙 P) i.hom) ≫ prod.snd =
        (m.left ≫ prod.lift _ (rR ≫ R.cons)) ≫ prod.snd
      simp only [Category.assoc, prod.map_snd, prod.lift_snd]
      rw [← Category.assoc, prod.lift_snd, Category.assoc, hc]
      exact (Category.assoc rS (prod.map (𝟙 V) i.hom) R.cons).symm.trans
        ((congrArg (fun k => k ≫ R.cons) hr.symm).trans
          (Category.assoc m.left rR R.cons))

def stableListOnIso (L : StableListAlgebra V) {X : C} (i : L.algebra.carrier ≅ X) :
    StableListAlgebra V where
  algebra := listOnIso L.algebra i
  initial := L.initial.ofIso (listOnIsoComparison L.algebra i)
  stable P := (L.stable P).ofIso (listParameterIso L.algebra (listOnIso L.algebra i) i
    (SyntaxOperationsTransport.listHom_nil (listOnIsoComparison L.algebra i).hom)
    (SyntaxOperationsTransport.listHom_cons (listOnIsoComparison L.algebra i).hom) P)

end Lists

section LiteralWords
variable (V : NumericalTuples.Object) (σ π : ℕ → NumericalTuples.Object) (d : ℕ)
local notation "S₀" => literalSourceSyntax V σ π d
local notation "S₁" => literalCategoricalSyntax V σ π d
local notation "K" => SyntaxPolynomial.jointFunctor
  (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d)

def literalWordPairIso : (S₁).algebra.a ≅
    (NumericalCoordinates.predicateObject (S₀).algebra.a.1,
      NumericalCoordinates.predicateObject (S₀).algebra.a.2) where
  hom := ((literalTermPresentationIso V σ π d).hom,
    (literalFormulaPresentationIso V σ π d).hom)
  inv := ((literalTermPresentationIso V σ π d).inv,
    (literalFormulaPresentationIso V σ π d).inv)
  hom_inv_id := Prod.ext (literalTermPresentationIso V σ π d).hom_inv_id
    (literalFormulaPresentationIso V σ π d).hom_inv_id
  inv_hom_id := Prod.ext (literalTermPresentationIso V σ π d).inv_hom_id
    (literalFormulaPresentationIso V σ π d).inv_hom_id

def literalWordAlgebra : Endofunctor.Algebra (K) :=
  algebraOnIso (K) (S₁).algebra (literalWordPairIso V σ π d)

def literalWordAlgebraIso : (S₁).algebra ≅ literalWordAlgebra V σ π d :=
  algebraOnIsoComparison (K) (S₁).algebra (literalWordPairIso V σ π d)

abbrev literal_word_constructor_comparison := (literalWordAlgebraIso V σ π d).hom.h

def literalWordInitial : IsInitial (literalWordAlgebra V σ π d) :=
  (S₁).initial.ofIso (literalWordAlgebraIso V σ π d)

def literalWordParameterIso (P : NumericalTuples.Object) :
    SyntaxPolynomial.algebraWithParameters
      (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d)
      (S₁).algebra P ≅
    SyntaxPolynomial.algebraWithParameters
      (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d)
      (literalWordAlgebra V σ π d) P :=
  SyntacticSyntax.parameterAlgebraIso _ _ P (literalWordAlgebraIso V σ π d)

def literalWordParameterInitial (P : NumericalTuples.Object) :
    IsInitial (SyntaxPolynomial.algebraWithParameters
      (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d)
      (literalWordAlgebra V σ π d) P) :=
  ((S₁).stable P).ofIso (literalWordParameterIso V σ π d P)

def literalWordLists : StableListAlgebra V :=
  stableListOnIso (S₁).lists (literalListPresentationIso V σ π d)

def literalWordListIso : (S₁).lists.algebra.asAlgebra ≅
    (literalWordLists V σ π d).algebra.asAlgebra :=
  listOnIsoComparison (S₁).lists.algebra (literalListPresentationIso V σ π d)

abbrev literal_word_nil_comparison :=
  SyntaxOperationsTransport.listHom_nil (literalWordListIso V σ π d).hom

abbrev literal_word_cons_comparison :=
  SyntaxOperationsTransport.listHom_cons (literalWordListIso V σ π d).hom

local notation "a₀" => SyntaxPolynomial.termExpression (D := PredicateCategory 𝗧𝗔) (NumericalCoordinates.codedPredicate V)
  (fun n => NumericalCoordinates.codedPredicate (σ n)) d
local notation "b₀" => SyntaxPolynomial.formulaExpression (D := PredicateCategory 𝗧𝗔) (NumericalCoordinates.codedPredicate V)
  (fun n => NumericalCoordinates.codedPredicate (π n)) d

def literalWordTermInputPresentationIso :
    (SyntaxPolynomial.termExpression V σ d).eval.obj (literalWordAlgebra V σ π d).a ≅
      NumericalCoordinates.predicateObject ((a₀).eval.obj (S₀).algebra.a) :=
  (SyntaxPolynomial.termExpression V σ d).eval.mapIso (literalWordPairIso V σ π d).symm ≪≫
    literalTermConstructorInputPresentationIso V σ π d

def literalWordFormulaInputPresentationIso :
    (SyntaxPolynomial.formulaExpression V π d).eval.obj (literalWordAlgebra V σ π d).a ≅
      NumericalCoordinates.predicateObject ((b₀).eval.obj (S₀).algebra.a) :=
  (SyntaxPolynomial.formulaExpression V π d).eval.mapIso (literalWordPairIso V σ π d).symm ≪≫
    literalFormulaConstructorInputPresentationIso V σ π d

theorem literal_wordTermConstructor_code_square :
    (literalWordAlgebra V σ π d).str.1 ≫
        (Iso.refl (NumericalCoordinates.predicateObject (S₀).algebra.a.1)).hom =
      (literalWordTermInputPresentationIso V σ π d).hom ≫
        NumericalCoordinates.predicateMap (S₀).algebra.str.1 :=
  operation_precompose_square (S₁).algebra.str.1 (literalTermPresentationIso V σ π d)
    (literalTermConstructorInputPresentationIso V σ π d).hom
    (NumericalCoordinates.predicateMap (S₀).algebra.str.1)
    (literal_termConstructor_code_square V σ π d)
    ((SyntaxPolynomial.termExpression V σ d).eval.map (literalWordPairIso V σ π d).inv)

theorem literal_wordFormulaConstructor_code_square :
    (literalWordAlgebra V σ π d).str.2 ≫
        (Iso.refl (NumericalCoordinates.predicateObject (S₀).algebra.a.2)).hom =
      (literalWordFormulaInputPresentationIso V σ π d).hom ≫
        NumericalCoordinates.predicateMap (S₀).algebra.str.2 :=
  operation_precompose_square (S₁).algebra.str.2 (literalFormulaPresentationIso V σ π d)
    (literalFormulaConstructorInputPresentationIso V σ π d).hom
    (NumericalCoordinates.predicateMap (S₀).algebra.str.2)
    (literal_formulaConstructor_code_square V σ π d)
    ((SyntaxPolynomial.formulaExpression V π d).eval.map (literalWordPairIso V σ π d).inv)

theorem literal_wordTermConstructor_value (x : NumericalTuples.Point
    ((SyntaxPolynomial.termExpression V σ d).eval.obj (literalWordAlgebra V σ π d).a)) :
    ((literalWordAlgebra V σ π d).str.1.toFun x).val =
      SyntacticSyntax.Coding.constructor false (a₀)
        (((SyntacticLists.F 𝗧𝗔 ℕ).map (NumericalSyntaxTreeChart.plainRawInput 𝗧𝗔 (a₀) (b₀)))
          ((literalWordTermInputPresentationIso V σ π d).hom.toFun x)).val :=
  predicate_operation_value (S₀).algebra.str.1 (literalWordAlgebra V σ π d).str.1
    (literalWordTermInputPresentationIso V σ π d)
    (Iso.refl (NumericalCoordinates.predicateObject (S₀).algebra.a.1))
    (literal_wordTermConstructor_code_square V σ π d) Subtype.val _
    (NumericalSyntaxTreeChart.plainTerm_constructor_value 𝗧𝗔 (a₀) (b₀) ℕ) x

theorem literal_wordFormulaConstructor_value (x : NumericalTuples.Point
    ((SyntaxPolynomial.formulaExpression V π d).eval.obj (literalWordAlgebra V σ π d).a)) :
    ((literalWordAlgebra V σ π d).str.2.toFun x).val =
      SyntacticSyntax.Coding.constructor true (b₀)
        (((SyntacticLists.F 𝗧𝗔 ℕ).map (plainFormulaRawInput 𝗧𝗔 (a₀) (b₀)))
          ((literalWordFormulaInputPresentationIso V σ π d).hom.toFun x)).val :=
  predicate_operation_value (S₀).algebra.str.2 (literalWordAlgebra V σ π d).str.2
    (literalWordFormulaInputPresentationIso V σ π d)
    (Iso.refl (NumericalCoordinates.predicateObject (S₀).algebra.a.2))
    (literal_wordFormulaConstructor_code_square V σ π d) Subtype.val _
    (plainFormula_constructor_value 𝗧𝗔 (a₀) (b₀) ℕ) x

def literalWordListConsInputPresentationIso :
    V ⨯ (literalWordLists V σ π d).algebra.carrier ≅
      NumericalCoordinates.predicateObject
        (NumericalCoordinates.codedPredicate V ⨯ (S₀).lists.algebra.carrier) :=
  prod.mapIso (Iso.refl V) (literalListPresentationIso V σ π d).symm ≪≫
    literalListConsInputPresentationIso V σ π d

theorem literal_wordListCons_code_square :
    (literalWordLists V σ π d).algebra.cons ≫
        (Iso.refl (NumericalCoordinates.predicateObject (S₀).lists.algebra.carrier)).hom =
      (literalWordListConsInputPresentationIso V σ π d).hom ≫
        NumericalCoordinates.predicateMap (S₀).lists.algebra.cons :=
  operation_precompose_square (S₁).lists.algebra.cons (literalListPresentationIso V σ π d)
    (literalListConsInputPresentationIso V σ π d).hom
    (NumericalCoordinates.predicateMap (S₀).lists.algebra.cons)
    (literal_listCons_code_square V σ π d)
    (prod.map (𝟙 V) (literalListPresentationIso V σ π d).inv)

theorem literal_wordListNil_value (x : NumericalTuples.Point (⊤_ NumericalTuples.Object)) :
    ((literalWordLists V σ π d).algebra.nil.toFun x).val = (0 : ℕ) :=
  literal_listNil_value V σ π d x

theorem literal_wordListCons_value
    (x : NumericalTuples.Point (V ⨯ (literalWordLists V σ π d).algebra.carrier)) :
    let x₀ := (literalWordListConsInputPresentationIso V σ π d).hom.toFun x
    ((literalWordLists V σ π d).algebra.cons.toFun x).val =
      adjoin (((PredicateInterpretation.functor 𝗧𝗔 ℕ).map
        (prod.fst : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance
          (NumericalCoordinates.codedPredicate V ⨯ (S₀).lists.algebra.carrier)
          (NumericalCoordinates.codedPredicate V))) x₀).val
        (((PredicateInterpretation.functor 𝗧𝗔 ℕ).map
          (prod.snd : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance
            (NumericalCoordinates.codedPredicate V ⨯ (S₀).lists.algebra.carrier)
            (S₀).lists.algebra.carrier)) x₀).val :=
  predicate_operation_value (S₀).lists.algebra.cons (literalWordLists V σ π d).algebra.cons
    (literalWordListConsInputPresentationIso V σ π d)
    (Iso.refl (NumericalCoordinates.predicateObject (S₀).lists.algebra.carrier))
    (literal_wordListCons_code_square V σ π d) Subtype.val _
    (SyntacticLists.cons_value 𝗧𝗔 ℕ (NumericalCoordinates.codedPredicate V)) x

end LiteralWords
end CategoricalEssentialIncompleteness.V46.NumericalNamed
