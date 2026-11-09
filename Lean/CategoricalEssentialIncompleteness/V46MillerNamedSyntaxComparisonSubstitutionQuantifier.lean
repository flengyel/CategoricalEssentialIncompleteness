import CategoricalEssentialIncompleteness.V46MillerNamedSyntaxComparisonSubstitutionState

/-! # Actual quantified-substitution branch comparison

The equal-name branch retains the original body, even when the recursive
option result is failure. Every Boolean/list/constructor comparison below
is derived for the concrete records; none is a final diagram premise.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntaxOperationsTransport
namespace CategoricalEssentialIncompleteness.V46.Miller.NamedSyntaxComparison
variable (P : Uniform.Family) (V : PredicateCategory 𝗣𝗔) (σ π : ℕ → PredicateCategory 𝗣𝗔) (d : ℕ)
local notation "F" => Syntax.predicateFunctor P
local notation "S₀" => sourceSyntax V σ π d
local notation "S₁" => presentedSyntax P V σ π d
local notation "ℓ" => Iso.refl (Functor.obj (Syntax.predicateFunctor P) (ListAlgebra.carrier (StableListAlgebra.algebra (CategoricalSyntax.lists (sourceSyntax V σ π d)))))

private theorem inverse_chart_square {X Y Z : Total.TotalCategory P} (i : X ≅ Y)
    (f : Y ⟶ Z) (g : X ⟶ Z) (h : i.hom ≫ f = g) : f = i.inv ≫ g := by
  calc
    _ = (i.inv ≫ i.hom) ≫ f := by rw [i.inv_hom_id,Category.id_comp]
    _ = _ := by rw [Category.assoc,h]

theorem substitution_composite_square
    {X Y Z : PredicateCategory 𝗣𝗔} {X' Y' Z' : Total.TotalCategory P}
    (k : (F).obj X ≅ X') (i : (F).obj Y ≅ Y') (j : (F).obj Z ≅ Z')
    (a : X ⟶ Y) (b : Y ⟶ Z) (a' : X' ⟶ Y') (b' : Y' ⟶ Z')
    (ha : (F).map a ≫ i.hom = k.hom ≫ a')
    (hb : (F).map b ≫ j.hom = i.hom ≫ b') :
    (F).map (a ≫ b) ≫ j.hom = k.hom ≫ a' ≫ b' := by
  rw [CategoryTheory.Functor.map_comp,Category.assoc,hb,← Category.assoc,ha,Category.assoc]

private theorem membership_comparison :
    (F).map ((S₀).lists.membership (S₀).decidableVariables) ≫ (Derivation.booleanIso (F)).hom=
      (Options.productIso (F) (Iso.refl ((F).obj V)) (ℓ)).hom ≫
        (S₁).lists.membership (S₁).decidableVariables := by
  simp only [Options.productIso,Iso.refl_hom,Iso.trans_hom,prod.mapIso_hom,
    prod.map_id_id,Category.comp_id,asIso_hom]
  change (F).map ((SyntacticLists.stableListAlgebra 𝗣𝗔 V).membership
      (S₀).decidableVariables) ≫ (Derivation.booleanIso (F)).hom =
    prodComparison (F) V (SyntacticLists.stableListAlgebra 𝗣𝗔 V).algebra.carrier ≫
      (mappedListStable P V).membership (Derivation.mappedEquality (F) (S₀).decidableVariables)
  exact ListTransport.map_membership P V (S₀).decidableVariables

private theorem formulaOccurrences_image :
    (F).map (S₀).formulaOccurrences ≫ (ℓ).hom=
      (formulaIso P V σ π d).inv ≫ (S₁).formulaOccurrences := by
  simp only [Iso.refl_hom,Category.comp_id]
  change (F).map (S₀).formulaOccurrences =
    (formulaIso P V σ π d).inv ≫ (S₁).formulaOccurrences
  exact inverse_chart_square P (formulaIso P V σ π d)
    ((F).map (S₀).formulaOccurrences) (S₁).formulaOccurrences
    (formulaOccurrences_comparison P V σ π d)

private theorem termOccurrences_image :
    (F).map (S₀).termOccurrences ≫ (ℓ).hom=
      (termIso P V σ π d).inv ≫ (S₁).termOccurrences := by
  simp only [Iso.refl_hom,Category.comp_id]
  change (F).map (S₀).termOccurrences =
    (termIso P V σ π d).inv ≫ (S₁).termOccurrences
  exact inverse_chart_square P (termIso P V σ π d)
    ((F).map (S₀).termOccurrences) (S₁).termOccurrences
    (termOccurrences_comparison P V σ π d)

theorem substitution_membership_square {X A B : PredicateCategory 𝗣𝗔} {X' A' B' : Total.TotalCategory P}
    (k : (F).obj X ≅ X') (i : (F).obj A ≅ A') (j : (F).obj B ≅ B')
    (a : X ⟶ A) (b : X ⟶ B) (a' : X' ⟶ A') (b' : X' ⟶ B')
    (m : A ⨯ B ⟶ Two (PredicateCategory 𝗣𝗔)) (m' : A' ⨯ B' ⟶ Two (Total.TotalCategory P))
    (ha : (F).map a ≫ i.hom = k.hom ≫ a')
    (hb : (F).map b ≫ j.hom = k.hom ≫ b')
    (hm : (F).map m ≫ (Derivation.booleanIso (F)).hom =
      (Options.productIso (F) i j).hom ≫ m') :
    (F).map (prod.lift a b ≫ m) ≫ (Derivation.booleanIso (F)).hom =
      k.hom ≫ (prod.lift a' b' ≫ m') := by
  rw [CategoryTheory.Functor.map_comp,Category.assoc,hm,← Category.assoc,Options.map_lift,
    ha,hb,← prod.comp_lift,Category.assoc]

theorem substitution_branch_square {X Y : PredicateCategory 𝗣𝗔} {X' Y' : Total.TotalCategory P}
    (k : (F).obj X ≅ X') (j : (F).obj Y ≅ Y')
    (χ : X ⟶ Two (PredicateCategory 𝗣𝗔)) (χ' : X' ⟶ Two (Total.TotalCategory P))
    (f g : X ⟶ Y) (f' g' : X' ⟶ Y')
    (hχ : (F).map χ ≫ (Derivation.booleanIso (F)).hom = k.hom ≫ χ')
    (hf : (F).map f ≫ j.hom = k.hom ≫ f')
    (hg : (F).map g ≫ j.hom = k.hom ≫ g') :
    (F).map (Two.branch χ f g) ≫ j.hom = k.hom ≫ Two.branch χ' f' g' := by
  rw [ListTransport.map_branch (F) χ f g,
    SyntaxOperationsTransport.transport_branch_postcomp,hχ,hf,hg,
    SyntaxOperationsTransport.branch_precomp]

theorem map_quantifierEquality :
    (F).map (S₀).quantifierEquality ≫ (Derivation.booleanIso (F)).hom =
      (substitutionQuantifierInputIso P V σ π d).hom ≫ (S₁).quantifierEquality := by
  let e : (F).obj V ≅ (F).obj V := Iso.refl ((F).obj V)
  let k : (F).obj ((S₀).substitutionParameters ⨯ (V ⨯ (S₀).substitutionCarriers.2)) ≅
      (S₁).substitutionParameters ⨯ ((F).obj V ⨯ (S₁).substitutionCarriers.2) :=
    substitutionQuantifierInputIso P V σ π d
  let a : (S₀).substitutionParameters ⨯ (V ⨯ (S₀).substitutionCarriers.2) ⟶
      V ⨯ V :=
    prod.lift (prod.snd ≫ prod.fst) (prod.fst ≫ prod.fst)
  let a' : (S₁).substitutionParameters ⨯ (((F).obj V) ⨯ (S₁).substitutionCarriers.2) ⟶ ((F).obj V) ⨯ ((F).obj V) :=
    prod.lift (prod.snd ≫ prod.fst) (prod.fst ≫ prod.fst)
  have ha : (F).map a ≫ (Options.productIso (F) e e).hom = k.hom ≫ a' := by
    change (F).map (prod.lift _ _) ≫ _ = _ ≫ prod.lift _ _
    rw [Options.map_lift,prod.comp_lift]
    exact congrArg₂ (fun x y => prod.lift x y)
      (substitutionQuantifierInput_binder P V σ π d).symm
      (substitutionQuantifierInput_query P V σ π d).symm
  have he := ListTransport.map_decidable_test (F) (S₀).decidableVariables
  have he' : (F).map (S₀).decidableVariables.test ≫ (Derivation.booleanIso (F)).hom =
      (Options.productIso (F) e e).hom ≫ (S₁).decidableVariables.test := by
    simp only [e,Options.productIso,Iso.trans_hom,prod.mapIso_hom,Iso.refl_hom,
      prod.map_id_id,Category.comp_id,asIso_hom]
    change (F).map (S₀).decidableVariables.test ≫ (Derivation.booleanIso (F)).hom =
      prodComparison (F) V V ≫ (Derivation.mappedEquality (F) (S₀).decidableVariables).test
    exact he
  change (F).map (a ≫ (S₀).decidableVariables.test) ≫ _ =
    k.hom ≫ (a' ≫ (S₁).decidableVariables.test)
  rw [CategoryTheory.Functor.map_comp,Category.assoc,he',← Category.assoc,ha,Category.assoc]

theorem map_captureAllowed :
    (F).map (S₀).captureAllowed ≫ (Derivation.booleanIso (F)).hom =
      (substitutionQuantifierInputIso P V σ π d).hom ≫ (S₁).captureAllowed := by
  let k : (F).obj ((S₀).substitutionParameters ⨯ (V ⨯ (S₀).substitutionCarriers.2)) ≅
      (S₁).substitutionParameters ⨯ ((F).obj V ⨯ (S₁).substitutionCarriers.2) :=
    substitutionQuantifierInputIso P V σ π d
  let e : (F).obj V ≅ (F).obj V := Iso.refl ((F).obj V)
  have hbody : (F).map
      (((prod.snd : (S₀).substitutionParameters ⨯
        (V ⨯ (S₀).substitutionCarriers.2) ⟶ _) ≫ prod.snd ≫ prod.fst) ≫
          (S₀).formulaOccurrences) ≫ (ℓ).hom =
      k.hom ≫ (prod.snd ≫ prod.snd ≫ prod.fst ≫ (S₁).formulaOccurrences) := by
    simpa only [Category.assoc] using
      (substitution_composite_square P k (formulaIso P V σ π d).symm (ℓ)
        ((prod.snd : (S₀).substitutionParameters ⨯
          (V ⨯ (S₀).substitutionCarriers.2) ⟶ V ⨯ (S₀).substitutionCarriers.2) ≫
            prod.snd ≫ prod.fst)
        (S₀).formulaOccurrences (prod.snd ≫ prod.snd ≫ prod.fst) (S₁).formulaOccurrences
        (substitutionQuantifierInput_originalBody P V σ π d).symm
        (formulaOccurrences_image P V σ π d))
  have hreplacement : (F).map
      (((prod.fst : (S₀).substitutionParameters ⨯
        (V ⨯ (S₀).substitutionCarriers.2) ⟶ _) ≫ prod.snd) ≫
          (S₀).termOccurrences) ≫ (ℓ).hom =
      k.hom ≫ (prod.fst ≫ prod.snd ≫ (S₁).termOccurrences) := by
    simpa only [Category.assoc] using
      (substitution_composite_square P k (termIso P V σ π d).symm (ℓ)
        ((prod.fst : (S₀).substitutionParameters ⨯
          (V ⨯ (S₀).substitutionCarriers.2) ⟶ (S₀).substitutionParameters) ≫ prod.snd)
        (S₀).termOccurrences (prod.fst ≫ prod.snd) (S₁).termOccurrences
        (substitutionQuantifierInput_replacement P V σ π d).symm
        (termOccurrences_image P V σ π d))
  have hm₀ := substitution_membership_square P
    (X := (S₀).substitutionParameters ⨯ (V ⨯ (S₀).substitutionCarriers.2))
    (A := V) (B := (S₀).lists.algebra.carrier)
    (X' := (S₁).substitutionParameters ⨯ ((F).obj V ⨯ (S₁).substitutionCarriers.2))
    (A' := (F).obj V) (B' := (S₁).lists.algebra.carrier) k e (ℓ)
    ((prod.fst : (S₀).substitutionParameters ⨯
      (V ⨯ (S₀).substitutionCarriers.2) ⟶ _) ≫ prod.fst)
    (prod.snd ≫ prod.snd ≫ prod.fst ≫ (S₀).formulaOccurrences)
    (prod.fst ≫ prod.fst) (prod.snd ≫ prod.snd ≫ prod.fst ≫ (S₁).formulaOccurrences)
    ((S₀).lists.membership (S₀).decidableVariables) ((S₁).lists.membership (S₁).decidableVariables)
    (substitutionQuantifierInput_query P V σ π d).symm (by simpa only [Category.assoc] using hbody) (membership_comparison P V σ π d)
  have hm₁ := substitution_membership_square P
    (X := (S₀).substitutionParameters ⨯ (V ⨯ (S₀).substitutionCarriers.2))
    (A := V) (B := (S₀).lists.algebra.carrier)
    (X' := (S₁).substitutionParameters ⨯ ((F).obj V ⨯ (S₁).substitutionCarriers.2))
    (A' := (F).obj V) (B' := (S₁).lists.algebra.carrier) k e (ℓ)
    ((prod.snd : (S₀).substitutionParameters ⨯
      (V ⨯ (S₀).substitutionCarriers.2) ⟶ _) ≫ prod.fst)
    (prod.fst ≫ prod.snd ≫ (S₀).termOccurrences)
    (prod.snd ≫ prod.fst) (prod.fst ≫ prod.snd ≫ (S₁).termOccurrences)
    ((S₀).lists.membership (S₀).decidableVariables) ((S₁).lists.membership (S₁).decidableVariables)
    (substitutionQuantifierInput_binder P V σ π d).symm (by simpa only [Category.assoc] using hreplacement) (membership_comparison P V σ π d)
  unfold CategoricalSyntax.captureAllowed
  rw [ListTransport.map_boolean_binary (F) Bool.or,ListTransport.map_boolean_unary (F) Bool.not,ListTransport.map_boolean_unary (F) Bool.not,
    hm₀,hm₁,Two.comp_binary,Two.comp_unary,Two.comp_unary]

theorem map_quantifierOriginal :
    (F).map (S₀).quantifierOriginal ≫ ((formulaIso P V σ π d).symm).hom =
      (substitutionQuantifierInputIso P V σ π d).hom ≫ (S₁).quantifierOriginal := by
  let k : (F).obj ((S₀).substitutionParameters ⨯ (V ⨯ (S₀).substitutionCarriers.2)) ≅
      (S₁).substitutionParameters ⨯ ((F).obj V ⨯ (S₁).substitutionCarriers.2) :=
    substitutionQuantifierInputIso P V σ π d
  let f : (F).obj (S₀).algebra.a.2 ≅ (S₁).algebra.a.2 :=
    (formulaIso P V σ π d).symm
  have hp : (F).map
      (prod.lift (prod.snd ≫ prod.fst)
        (prod.snd ≫ prod.snd ≫ prod.fst) :
        (S₀).substitutionParameters ⨯ (V ⨯ (S₀).substitutionCarriers.2) ⟶ _) ≫
      (Options.productIso (F) (Iso.refl ((F).obj V)) f).hom =
      k.hom ≫ prod.lift (prod.snd ≫ prod.fst) (prod.snd ≫ prod.snd ≫ prod.fst) := by
    rw [Options.map_lift,prod.comp_lift,
      substitutionQuantifierInput_binder P V σ π d,
      substitutionQuantifierInput_originalBody P V σ π d]
  exact substitution_composite_square P
    (X := (S₀).substitutionParameters ⨯ (V ⨯ (S₀).substitutionCarriers.2))
    (Y := V ⨯ (S₀).algebra.a.2) (Z := (S₀).algebra.a.2)
    (X' := (S₁).substitutionParameters ⨯ ((F).obj V ⨯ (S₁).substitutionCarriers.2))
    (Y' := (F).obj V ⨯ (S₁).algebra.a.2) (Z' := (S₁).algebra.a.2)
    k (Options.productIso (F) (Iso.refl ((F).obj V)) f) f
    (prod.lift (prod.snd ≫ prod.fst) (prod.snd ≫ prod.snd ≫ prod.fst))
    (S₀).quantifierConstructor
    (prod.lift (prod.snd ≫ prod.fst) (prod.snd ≫ prod.snd ≫ prod.fst))
    (S₁).quantifierConstructor hp (quantifier_constructor P V σ π d)

theorem map_quantifierSubstitutionResult :
    (F).map (S₀).quantifierSubstitutionResult ≫
        (Options.optionIso (F) ((formulaIso P V σ π d).symm)).hom =
      (substitutionQuantifierInputIso P V σ π d).hom ≫ (S₁).quantifierSubstitutionResult := by
  let k : (F).obj ((S₀).substitutionParameters ⨯ (V ⨯ (S₀).substitutionCarriers.2)) ≅
      (S₁).substitutionParameters ⨯ ((F).obj V ⨯ (S₁).substitutionCarriers.2) :=
    substitutionQuantifierInputIso P V σ π d
  let f : (F).obj (S₀).algebra.a.2 ≅ (S₁).algebra.a.2 :=
    (formulaIso P V σ π d).symm
  let o : (F).obj (OptionSyntax.obj (S₀).algebra.a.2) ≅ OptionSyntax.obj (S₁).algebra.a.2 :=
    Options.optionIso (F) f
  let a : (S₀).substitutionParameters ⨯ (V ⨯ (S₀).substitutionCarriers.2) ⟶
      V ⨯ OptionSyntax.obj (S₀).algebra.a.2 :=
    prod.lift (prod.snd ≫ prod.fst) (prod.snd ≫ prod.snd ≫ prod.snd)
  let a' : (S₁).substitutionParameters ⨯ (((F).obj V) ⨯ (S₁).substitutionCarriers.2) ⟶
      ((F).obj V) ⨯ OptionSyntax.obj (S₁).algebra.a.2 :=
    prod.lift (prod.snd ≫ prod.fst) (prod.snd ≫ prod.snd ≫ prod.snd)
  have ha : (F).map a ≫
      (Options.productIso (F) (Iso.refl ((F).obj V)) o).hom = k.hom ≫ a' := by
    change (F).map (prod.lift _ _) ≫ _ = _ ≫ prod.lift _ _
    rw [Options.map_lift,prod.comp_lift]
    exact congrArg₂ (fun x y => prod.lift x y)
      (substitutionQuantifierInput_binder P V σ π d).symm
      (substitutionQuantifierInput_bodyResult P V σ π d).symm
  have hcoef : (F).map (a ≫ OptionSyntax.coefficient (S₀).quantifierConstructor) ≫ o.hom =
      k.hom ≫ (a' ≫ OptionSyntax.coefficient (S₁).quantifierConstructor) := by
    rw [CategoryTheory.Functor.map_comp,Category.assoc,
      Options.map_coefficient (F) (Iso.refl ((F).obj V)) f f
        (S₀).quantifierConstructor (S₁).quantifierConstructor
        (quantifier_constructor P V σ π d),
      ← Category.assoc,ha,Category.assoc]
  have hfail : (F).map (OptionSyntax.fail :
      (S₀).substitutionParameters ⨯ (V ⨯ (S₀).substitutionCarriers.2) ⟶
        OptionSyntax.obj (S₀).algebra.a.2) ≫ o.hom = k.hom ≫ OptionSyntax.fail := by
    rw [Options.map_fail]
    simp only [OptionSyntax.fail,← Category.assoc,terminal.comp_from]
  have hinner := substitution_branch_square P k o (S₀).captureAllowed (S₁).captureAllowed
    OptionSyntax.fail (a ≫ OptionSyntax.coefficient (S₀).quantifierConstructor)
    OptionSyntax.fail (a' ≫ OptionSyntax.coefficient (S₁).quantifierConstructor)
    (map_captureAllowed P V σ π d)
    hfail hcoef
  have hold : (F).map ((S₀).quantifierOriginal ≫ coprod.inr) ≫ o.hom =
      k.hom ≫ ((S₁).quantifierOriginal ≫ coprod.inr) := by
    rw [Options.map_some,map_quantifierOriginal P V σ π d,Category.assoc]
  exact substitution_branch_square P k o (S₀).quantifierEquality (S₁).quantifierEquality _ _ _ _
    (map_quantifierEquality P V σ π d) hinner hold

theorem map_quantifierSubstitutionPair :
    (F).map (S₀).quantifierSubstitutionPair ≫
        (substitutionFormulaStateIso P V σ π d).hom =
      (substitutionQuantifierInputIso P V σ π d).hom ≫ (S₁).quantifierSubstitutionPair := by
  change (F).map (prod.lift _ _) ≫
    (Options.productIso (F) ((formulaIso P V σ π d).symm)
      (Options.optionIso (F) ((formulaIso P V σ π d).symm))).hom =
    _ ≫ prod.lift _ _
  rw [Options.map_lift,prod.comp_lift]
  exact congrArg₂ (fun f g => prod.lift f g)
    (map_quantifierOriginal P V σ π d)
    (map_quantifierSubstitutionResult P V σ π d)


theorem equal_name_keeps_original :
    Two.fiberι (S₁).quantifierEquality true ≫ (S₁).quantifierSubstitutionResult=
      Two.fiberι (S₁).quantifierEquality true ≫ (S₁).quantifierOriginal ≫ coprod.inr :=
  (S₁).quantifierSubstitution_equal_branch

/-- Equal binder/query names retain the original body with an explicitly
failed recursive result. No success or capture-avoidance premise is used. -/
theorem equal_name_keeps_original_with_recursive_failure {X : Total.TotalCategory P}
    (p : X ⟶ (S₁).substitutionParameters) (body : X ⟶ (S₁).algebra.a.2) :
    prod.lift p (prod.lift (p ≫ prod.fst)
      (prod.lift body (OptionSyntax.fail : X ⟶ OptionSyntax.obj (S₁).algebra.a.2))) ≫
        (S₁).quantifierSubstitutionResult =
      prod.lift (p ≫ prod.fst) body ≫ (S₁).quantifierConstructor ≫ coprod.inr := by
  let u : X ⟶ (S₁).substitutionParameters ⨯ ((F).obj V ⨯ (S₁).substitutionCarriers.2) :=
    prod.lift p (prod.lift (p ≫ prod.fst)
      (prod.lift body (OptionSyntax.fail : X ⟶ OptionSyntax.obj (S₁).algebra.a.2)))
  have he : u ≫ (S₁).quantifierEquality = Two.constant X true := by
    simpa only [u,CategoricalSyntax.quantifierEquality,Category.assoc,
      prod.comp_lift,prod.comp_lift_assoc,prod.lift_fst,prod.lift_fst_assoc,
      prod.lift_snd,prod.lift_snd_assoc] using
      ((S₁).decidableVariables.test_true_iff (p ≫ prod.fst) (p ≫ prod.fst)).mpr rfl
  change u ≫ (S₁).quantifierSubstitutionResult = _
  calc
    _ = u ≫ (S₁).quantifierOriginal ≫ coprod.inr := by
      exact Two.comp_branch (S₁).quantifierEquality
        (Two.branch (S₁).captureAllowed OptionSyntax.fail
          (prod.lift (prod.snd ≫ prod.fst) (prod.snd ≫ prod.snd ≫ prod.snd) ≫
            OptionSyntax.coefficient (S₁).quantifierConstructor))
        ((S₁).quantifierOriginal ≫ coprod.inr) u true he
    _ = _ := by
      simp only [u,CategoricalSyntax.quantifierOriginal,Category.assoc,
        prod.comp_lift_assoc,prod.lift_fst,prod.lift_snd_assoc]

end CategoricalEssentialIncompleteness.V46.Miller.NamedSyntaxComparison
