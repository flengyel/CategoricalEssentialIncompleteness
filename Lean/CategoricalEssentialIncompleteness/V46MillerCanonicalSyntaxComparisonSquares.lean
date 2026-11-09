import CategoricalEssentialIncompleteness.V46MillerCanonicalSyntaxComparisonSentences
import CategoricalEssentialIncompleteness.V46NumericalArithmeticDistributionTransport

/-! # Compositional squares for the actual logical parameter diagrams -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.Miller.CanonicalPresentation

section Geometry
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
variable {E : C ≌ D}

omit [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D] in
theorem square_comp {X Y Z : C} {X' Y' Z' : D}
    {i : E.functor.obj X ≅ X'} {j : E.functor.obj Y ≅ Y'} {k : E.functor.obj Z ≅ Z'}
    {f : X ⟶ Y} {g : Y ⟶ Z} {f' : X' ⟶ Y'} {g' : Y' ⟶ Z'}
    (hf : E.functor.map f ≫ j.hom = i.hom ≫ f')
    (hg : E.functor.map g ≫ k.hom = j.hom ≫ g') :
    E.functor.map (f ≫ g) ≫ k.hom = i.hom ≫ (f' ≫ g') := by
  rw [E.functor.map_comp, Category.assoc, hg, ← Category.assoc, hf, Category.assoc]

omit [FinitaryExtensive C] [FinitaryExtensive D] in
theorem square_lift {X Y Z : C} {X' Y' Z' : D}
    {i : E.functor.obj X ≅ X'} {j : E.functor.obj Y ≅ Y'} {k : E.functor.obj Z ≅ Z'}
    {f : X ⟶ Y} {g : X ⟶ Z} {f' : X' ⟶ Y'} {g' : X' ⟶ Z'}
    (hf : E.functor.map f ≫ j.hom = i.hom ≫ f')
    (hg : E.functor.map g ≫ k.hom = i.hom ≫ g') :
    E.functor.map (prod.lift f g) ≫ (SyntaxOptionTransport.productIso E j k).hom =
      i.hom ≫ prod.lift f' g' := by
  rw [SyntaxOptionTransport.map_lift, hf, hg, prod.comp_lift]

omit [FinitaryExtensive C] [FinitaryExtensive D] in
theorem square_fst {X Y : C} {X' Y' : D}
    (i : E.functor.obj X ≅ X') (j : E.functor.obj Y ≅ Y') :
    E.functor.map (prod.fst : X ⨯ Y ⟶ X) ≫ i.hom =
      (SyntaxOptionTransport.productIso E i j).hom ≫ prod.fst :=
  (SyntaxOptionTransport.productIso_fst E i j).symm

omit [FinitaryExtensive C] [FinitaryExtensive D] in
theorem square_snd {X Y : C} {X' Y' : D}
    (i : E.functor.obj X ≅ X') (j : E.functor.obj Y ≅ Y') :
    E.functor.map (prod.snd : X ⨯ Y ⟶ Y) ≫ j.hom =
      (SyntaxOptionTransport.productIso E i j).hom ≫ prod.snd :=
  (SyntaxOptionTransport.productIso_snd E i j).symm

omit [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D] in
theorem square_id {X : C} {X' : D} (i : E.functor.obj X ≅ X') :
    E.functor.map (𝟙 X) ≫ i.hom = i.hom ≫ 𝟙 X' := by simp

omit [Regular C] [Regular D] in
theorem square_desc {X Y Z : C} {X' Y' Z' : D}
    (i : E.functor.obj X ≅ X') (j : E.functor.obj Y ≅ Y') (k : E.functor.obj Z ≅ Z')
    {f : X ⟶ Z} {g : Y ⟶ Z} {f' : X' ⟶ Z'} {g' : Y' ⟶ Z'}
    (hf : E.functor.map f ≫ k.hom = i.hom ≫ f')
    (hg : E.functor.map g ≫ k.hom = j.hom ≫ g') :
    E.functor.map (coprod.desc f g) ≫ k.hom =
      (SyntaxOperationsTransport.sumInputIso E i j).hom ≫ coprod.desc f' g' := by
  apply BinaryCofan.IsColimit.hom_ext
    (isColimitOfHasBinaryCoproductOfPreservesColimit E.functor X Y)
  · change E.functor.map (coprod.inl : X ⟶ X ⨿ Y) ≫
        (E.functor.map (coprod.desc f g) ≫ k.hom) =
      E.functor.map (coprod.inl : X ⟶ X ⨿ Y) ≫
        ((SyntaxOperationsTransport.sumInputIso E i j).hom ≫ coprod.desc f' g')
    rw [← Category.assoc, ← E.functor.map_comp, coprod.inl_desc,
      ← Category.assoc, SyntaxOperationsTransport.sumInputIso_inl, Category.assoc, coprod.inl_desc]
    exact hf
  · change E.functor.map (coprod.inr : Y ⟶ X ⨿ Y) ≫
        (E.functor.map (coprod.desc f g) ≫ k.hom) =
      E.functor.map (coprod.inr : Y ⟶ X ⨿ Y) ≫
        ((SyntaxOperationsTransport.sumInputIso E i j).hom ≫ coprod.desc f' g')
    rw [← Category.assoc, ← E.functor.map_comp, coprod.inr_desc,
      ← Category.assoc, SyntaxOperationsTransport.sumInputIso_inr, Category.assoc, coprod.inr_desc]
    exact hg

variable (E)
variable {X Y Z : C} {X' Y' Z' : D}
variable (i : E.functor.obj X ≅ X') (j : E.functor.obj Y ≅ Y') (k : E.functor.obj Z ≅ Z')
variable (f : X ⟶ Z) (g : Y ⟶ Z) (f' : X' ⟶ Z') (g' : Y' ⟶ Z')
variable (hf : E.functor.map f ≫ k.hom = i.hom ≫ f')
variable (hg : E.functor.map g ≫ k.hom = j.hom ≫ g')

omit [FinitaryExtensive C] [FinitaryExtensive D] in
include hf hg in
theorem comparedPullback :
    IsPullback (E.functor.map (pullback.fst f g) ≫ i.hom)
      (E.functor.map (pullback.snd f g) ≫ j.hom) f' g' := by
  apply (E.functor.map_isPullback (IsPullback.of_hasPullback f g)).of_iso
    (Iso.refl _) i j k
  · simp
  · simp
  · exact hf
  · exact hg

def pullbackChart : E.functor.obj (pullback f g) ≅ pullback f' g' :=
  (comparedPullback E i j k f g f' g' hf hg).isoPullback

omit [FinitaryExtensive C] [FinitaryExtensive D] in
theorem pullbackChart_fst :
    E.functor.map (pullback.fst f g) ≫ i.hom =
      (pullbackChart E i j k f g f' g' hf hg).hom ≫ pullback.fst f' g' :=
  (comparedPullback E i j k f g f' g' hf hg).isoPullback_hom_fst.symm

omit [FinitaryExtensive C] [FinitaryExtensive D] in
theorem pullbackChart_snd :
    E.functor.map (pullback.snd f g) ≫ j.hom =
      (pullbackChart E i j k f g f' g' hf hg).hom ≫ pullback.snd f' g' :=
  (comparedPullback E i j k f g f' g' hf hg).isoPullback_hom_snd.symm

omit [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D] in
private theorem equivalence_symm_symm (e : C ≌ D) : e.symm.symm = e := by
  cases e
  rfl

omit [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D] in
private theorem transpose_square_symm (e : C ≌ D) {X Y : D} {X' Y' : C}
    (i : e.inverse.obj X ≅ X') (j : e.inverse.obj Y ≅ Y')
    (f : X ⟶ Y) (g : X' ⟶ Y')
    (h : e.inverse.map f ≫ j.hom = i.hom ≫ g) :
    e.functor.map g ≫ (transposeIso e.symm j).hom =
      (transposeIso e.symm i).hom ≫ f := by
  simpa only [CategoryTheory.Equivalence.symm] using transpose_square e.symm i j f g h

omit [FinitaryExtensive C] [FinitaryExtensive D] in
private theorem transpose_product_symm (e : C ≌ D) {X Y : D} {X' Y' : C}
    (i : e.inverse.obj X ≅ X') (j : e.inverse.obj Y ≅ Y') :
    transposeIso e.symm (SyntaxOptionTransport.productIso e.symm i j) =
      SyntaxOptionTransport.productIso e (transposeIso e.symm i) (transposeIso e.symm j) := by
  refine (transpose_product e.symm i j).trans ?_
  apply Iso.ext
  rfl

private theorem transpose_boolean_symm (e : C ≌ D) :
    transposeIso e.symm (DecidableVariables.Transport.booleanIso e.symm) =
      DecidableVariables.Transport.booleanIso e := by
  refine (transpose_boolean e.symm).trans ?_
  apply Iso.ext
  rfl
end Geometry

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open SyntacticPredicates SyntaxOperationsTransport
variable (a : Point) (V : PredicateCategory 𝗣𝗔)
variable (σ π : ℕ → PredicateCategory 𝗣𝗔) (d : ℕ)
local notation "P" => Uniform.Family.ofPoint a
local notation "F" => Syntax.predicateFunctor (P)
local notation "E" => Total.pointPresentation a
local notation "v" => CategoryTheory.Functor.obj (Syntax.predicateFunctor (Uniform.Family.ofPoint a)) V
local notation "s" => (fun n => CategoryTheory.Functor.obj (Syntax.predicateFunctor (Uniform.Family.ofPoint a)) (σ n))
local notation "r" => (fun n => CategoryTheory.Functor.obj (Syntax.predicateFunctor (Uniform.Family.ofPoint a)) (π n))
local notation "S₁" => NamedSyntaxComparison.presentedSyntax (P) V σ π d
local notation "S₂" => NamedSyntaxComparison.canonicalPresentedSyntax a V σ π d

def nameIso : (E).functor.obj (v) ≅ (E).functor.obj (v) :=
  transposeIso (E).symm ((E).symm.counitIso.app (v))

theorem nameIso_eq_refl : nameIso a V = Iso.refl ((E).functor.obj (v)) :=
  transpose_unit_inverse (E) (v)

theorem list_cons_comparison :
    (E).functor.map (S₁).lists.algebra.cons ≫ (listIso a V σ π d).hom =
      (SyntaxOptionTransport.productIso (E) (nameIso a V) (listIso a V σ π d)).hom ≫
        (S₂).lists.algebra.cons := by
  rw [listIso_eq_refl, nameIso_eq_refl]
  change (E).functor.map (S₁).lists.algebra.cons ≫
      𝟙 ((E).functor.obj (S₁).lists.algebra.carrier) =
    (SyntaxOptionTransport.productIso (E) (Iso.refl ((E).functor.obj (v)))
      (Iso.refl ((E).functor.obj (S₁).lists.algebra.carrier))).hom ≫
        (SyntacticLists.Transport.mappedStableListAlgebra (E) (v)
          ((E).functor.obj (v)) (Iso.refl _) (S₁).lists).algebra.cons
  simpa only [SyntaxOptionTransport.productIso, Iso.trans_hom, asIso_hom,
    prod.mapIso_hom, Iso.refl_hom, prod.map_id_id, Category.comp_id, Category.id_comp]
    using SyntaxOperationsTransport.map_list_cons (E) (v) ((E).functor.obj (v)) (Iso.refl _) (S₁).lists

theorem list_singleton_comparison :
    (E).functor.map (S₁).lists.singleton ≫ (listIso a V σ π d).hom =
      (nameIso a V).hom ≫ (S₂).lists.singleton := by
  exact transpose_square_symm (E) ((E).symm.counitIso.app (v)) (reverseLists a V σ π d)
    (S₂).lists.singleton (S₁).lists.singleton (reverse_singleton a V σ π d)

theorem list_append_comparison :
    (E).functor.map (S₁).lists.append ≫ (listIso a V σ π d).hom =
      (SyntaxOptionTransport.productIso (E) (listIso a V σ π d) (listIso a V σ π d)).hom ≫
        (S₂).lists.append := by
  have h := transpose_square_symm (E)
    (SyntaxOptionTransport.productIso (E).symm (reverseLists a V σ π d) (reverseLists a V σ π d))
    (reverseLists a V σ π d) (S₂).lists.append (S₁).lists.append (reverse_append a V σ π d)
  simpa only [transpose_product_symm, listIso] using h

theorem list_deletion_comparison :
    (E).functor.map ((S₁).lists.deletion (S₁).decidableVariables) ≫ (listIso a V σ π d).hom =
      (SyntaxOptionTransport.productIso (E) (nameIso a V) (listIso a V σ π d)).hom ≫
        (S₂).lists.deletion (S₂).decidableVariables := by
  have h := transpose_square_symm (E)
    (SyntaxOptionTransport.productIso (E).symm ((E).symm.counitIso.app (v)) (reverseLists a V σ π d))
    (reverseLists a V σ π d) ((S₂).lists.deletion (S₂).decidableVariables)
    ((S₁).lists.deletion (S₁).decidableVariables) (reverse_deletion a V σ π d)
  simpa only [transpose_product_symm, nameIso, listIso] using h

theorem parameterIso_product : parameterIso a V σ π d =
    SyntaxOptionTransport.productIso (E) (nameIso a V) (termIso a V σ π d) :=
  transpose_product_symm (E) ((E).symm.counitIso.app (v)) (reverseTermIso a V σ π d)

theorem implication_comparison :
    (E).functor.map (S₁).implicationConstructor ≫ (formulaIso a V σ π d).hom =
      (SyntaxOptionTransport.productIso (E) (formulaIso a V σ π d)
        (formulaIso a V σ π d)).hom ≫ (S₂).implicationConstructor := by
  have h := transpose_square_symm (E)
    (SyntaxOptionTransport.productIso (E).symm (reverseFormulaIso a V σ π d)
      (reverseFormulaIso a V σ π d)) (reverseFormulaIso a V σ π d)
    (S₂).implicationConstructor (S₁).implicationConstructor
    (syntax_implication_constructor (E).symm (v) (s) (r) d (S₂) (S₁) (reverseAlgebraIso a V σ π d))
  simpa only [transpose_product_symm, formulaIso] using h

theorem equality_comparison :
    (E).functor.map (S₁).equalityConstructor ≫ (formulaIso a V σ π d).hom =
      (SyntaxOptionTransport.productIso (E) (termIso a V σ π d)
        (termIso a V σ π d)).hom ≫ (S₂).equalityConstructor := by
  have h := transpose_square_symm (E)
    (SyntaxOptionTransport.productIso (E).symm (reverseTermIso a V σ π d)
      (reverseTermIso a V σ π d)) (reverseFormulaIso a V σ π d)
    (S₂).equalityConstructor (S₁).equalityConstructor
    (syntax_equality_constructor (E).symm (v) (s) (r) d (S₂) (S₁) (reverseAlgebraIso a V σ π d))
  simpa only [transpose_product_symm, termIso, formulaIso] using h

theorem quantifier_comparison :
    (E).functor.map (S₁).quantifierConstructor ≫ (formulaIso a V σ π d).hom =
      (SyntaxOptionTransport.productIso (E) (nameIso a V)
        (formulaIso a V σ π d)).hom ≫ (S₂).quantifierConstructor := by
  have h := transpose_square_symm (E)
    (SyntaxOptionTransport.productIso (E).symm ((E).symm.counitIso.app (v))
      (reverseFormulaIso a V σ π d)) (reverseFormulaIso a V σ π d)
    (S₂).quantifierConstructor (S₁).quantifierConstructor
    (syntax_quantifier_constructor (E).symm (v) (s) (r) d (S₂) (S₁) (reverseAlgebraIso a V σ π d))
  simpa only [transpose_product_symm, nameIso, formulaIso] using h

theorem membership_comparison :
    (E).functor.map ((S₁).lists.membership (S₁).decidableVariables) ≫
        (DecidableVariables.Transport.booleanIso (E)).hom =
      (SyntaxOptionTransport.productIso (E) (nameIso a V) (listIso a V σ π d)).hom ≫
        (S₂).lists.membership (S₂).decidableVariables := by
  have h := transpose_square_symm (E)
    (SyntaxOptionTransport.productIso (E).symm ((E).symm.counitIso.app (v))
      (reverseLists a V σ π d)) (DecidableVariables.Transport.booleanIso (E).symm)
    ((S₂).lists.membership (S₂).decidableVariables) ((S₁).lists.membership (S₁).decidableVariables)
    (reverse_membership a V σ π d)
  simpa only [transpose_product_symm, transpose_boolean_symm, nameIso, listIso] using h

end CategoricalEssentialIncompleteness.V46.Miller.CanonicalPresentation
