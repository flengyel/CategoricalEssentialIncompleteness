import CategoricalEssentialIncompleteness.V46CategoricalSubstitutionIdentityParameters
import CategoricalEssentialIncompleteness.V46CategoricalSubstitutionIdentityOptions
import CategoricalEssentialIncompleteness.V46CategoricalFreeVariableLaws

/-! Identity substitution for the actual named-variable substitution fold. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.CategoricalSyntax

open SyntaxParameterChange

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V : D} {σ π : ℕ → D} {d : ℕ} (S : CategoricalSyntax V σ π d)

attribute [local simp] prod.comp_lift_assoc prod.lift_fst_assoc prod.lift_snd_assoc
  prod.map_fst_assoc prod.map_snd_assoc

/-- The manuscript's identity parameter `x ↦ (x,ηx)`. -/
def identityParameters : V ⟶ S.substitutionParameters :=
  prod.lift (𝟙 V) S.variableConstructor

/-- The intended original/result pairs for successful identity substitution. -/
def identityPair : S.algebra.a ⟶ S.substitutionCarriers :=
  (prod.lift (𝟙 _) (𝟙 _), prod.lift (𝟙 _) coprod.inr)

@[simp] theorem identityPair_original : S.identityPair ≫ S.originalProjection = 𝟙 _ := by
  apply Prod.ext <;> simp [identityPair, originalProjection]

@[simp] theorem identityPair_result : S.identityPair ≫ S.termResultProjection = 𝟙 _ := by
  apply Prod.ext <;> simp [identityPair, termResultProjection]

def identityCandidate :
    ((Over.map S.identityParameters).obj (constantFamily V S.algebra.a.1),
      (Over.map S.identityParameters).obj (constantFamily V S.algebra.a.2)) ⟶
        S.substitutionAlgebra.a := by
  change ((Over.map S.identityParameters).obj (constantFamily V S.algebra.a.1),
    (Over.map S.identityParameters).obj (constantFamily V S.algebra.a.2)) ⟶
      (constantFamily S.substitutionParameters S.substitutionCarriers.1,
        constantFamily S.substitutionParameters S.substitutionCarriers.2)
  exact
    (baseMap S.identityParameters S.algebra.a.1 ≫
      (constantFamilyFunctor S.substitutionParameters).map S.identityPair.1,
    baseMap S.identityParameters S.algebra.a.2 ≫
      (constantFamilyFunctor S.substitutionParameters).map S.identityPair.2)

@[simp] theorem identityCandidate_term : S.identityCandidate.1 =
    baseMap S.identityParameters S.algebra.a.1 ≫
      (constantFamilyFunctor S.substitutionParameters).map S.identityPair.1 := rfl

@[simp] theorem identityCandidate_formula : S.identityCandidate.2 =
    baseMap S.identityParameters S.algebra.a.2 ≫
      (constantFamilyFunctor S.substitutionParameters).map S.identityPair.2 := rfl

theorem variable_identity_conditional {X : D} (u v : X ⟶ V) :
    Two.branch (prod.lift u v ≫ S.decidableVariables.test)
      (u ≫ S.variableConstructor) (v ≫ S.variableConstructor) = u ≫ S.variableConstructor := by
  let b := prod.lift u v ≫ S.decidableVariables.test
  apply Two.hom_ext b
  · exact Two.fiberι_branch b (u ≫ S.variableConstructor) (v ≫ S.variableConstructor) false
  · rw [Two.fiberι_branch]
    simp only [↓reduceIte]
    have h : Two.fiberι b true ≫ u = Two.fiberι b true ≫ v :=
      (S.decidableVariables.test_true_iff _ _).mp (by
        simpa only [b, prod.comp_lift_assoc] using Two.fiberι_comp b true)
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ S.variableConstructor) h.symm).trans (Category.assoc _ _ _))

theorem variable_identity_pair :
    prod.map S.identityParameters (𝟙 V) ≫ S.variableSubstitutionPair =
      prod.lift (prod.snd ≫ S.variableConstructor) (prod.snd ≫ S.variableConstructor) := by
  simp [variableSubstitutionPair, identityParameters, branch_natural,
    S.variable_identity_conditional]

theorem function_identity_pair :
    (SyntaxPolynomial.constructors σ d).eval.map S.identityPair ≫ S.functionSubstitutionPair =
      S.functionConstructors ≫ S.identityPair.1 := by
  simp only [functionSubstitutionPair, prod.comp_lift,
    ← CategoryTheory.Functor.map_comp_assoc, S.identityPair_original, S.identityPair_result,
    CategoryTheory.Functor.map_id, Category.id_comp]
  simp [identityPair]

theorem equality_identity_pair :
    (SyntaxPolynomial.power .term 2).eval.map S.identityPair ≫ S.equalitySubstitutionPair =
      S.equalityConstructor ≫ S.identityPair.2 := by
  simp only [equalitySubstitutionPair, prod.comp_lift,
    ← CategoryTheory.Functor.map_comp_assoc, S.identityPair_original, S.identityPair_result,
    CategoryTheory.Functor.map_id, Category.id_comp]
  simp [identityPair]

theorem relation_identity_pair :
    (SyntaxPolynomial.constructors π d).eval.map S.identityPair ≫ S.relationSubstitutionPair =
      S.relationConstructors ≫ S.identityPair.2 := by
  simp only [relationSubstitutionPair, prod.comp_lift,
    ← CategoryTheory.Functor.map_comp_assoc, S.identityPair_original, S.identityPair_result,
    CategoryTheory.Functor.map_id, Category.id_comp]
  simp [identityPair]

theorem negation_identity_pair :
    S.identityPair.2 ≫ S.negationSubstitutionPair = S.negationConstructor ≫ S.identityPair.2 := by
  simp [identityPair, negationSubstitutionPair, prod.comp_lift]

theorem implication_identity_pair :
    (SyntaxPolynomial.power .formula 2).eval.map S.identityPair ≫ S.implicationSubstitutionPair =
      S.implicationConstructor ≫ S.identityPair.2 := by
  simp [SyntaxPolynomial.power, SyntaxPolynomial.eval, SyntaxPolynomial.productFunctor,
    identityPair, implicationSubstitutionPair, prod.comp_lift]

def identityQuantifierInput : V ⨯ (V ⨯ S.algebra.a.2) ⟶
    S.substitutionParameters ⨯ (V ⨯ S.substitutionCarriers.2) :=
  prod.lift (prod.fst ≫ S.identityParameters)
    (prod.lift (prod.snd ≫ prod.fst) (prod.snd ≫ prod.snd ≫ S.identityPair.2))

@[simp, reassoc] theorem identity_quantifier_original :
    S.identityQuantifierInput ≫ S.quantifierOriginal = prod.snd ≫ S.quantifierConstructor := by
  simp [identityQuantifierInput, identityPair, quantifierOriginal]

@[simp, reassoc] theorem identity_quantifier_equality :
    S.identityQuantifierInput ≫ S.quantifierEquality =
      prod.lift (prod.snd ≫ prod.fst) prod.fst ≫ S.decidableVariables.test := by
  simp [identityQuantifierInput, identityParameters, quantifierEquality]

theorem identity_quantifier_capture :
    S.identityQuantifierInput ≫ S.captureAllowed =
      Two.binary Bool.or
        (Two.unary Bool.not
          (prod.lift prod.fst (prod.snd ≫ prod.snd ≫ S.formulaOccurrences) ≫
            S.lists.membership S.decidableVariables))
        (Two.unary Bool.not
          (prod.lift (prod.snd ≫ prod.fst) prod.fst ≫ S.decidableVariables.test)) := by
  simp [identityQuantifierInput, identityParameters, identityPair, captureAllowed,
    S.variable_membership]

theorem quantifier_identity_result :
    S.identityQuantifierInput ≫ S.quantifierSubstitutionResult =
      prod.snd ≫ S.quantifierConstructor ≫ coprod.inr := by
  let b : V ⨯ (V ⨯ S.algebra.a.2) ⟶ Two D :=
    prod.lift (prod.snd ≫ prod.fst) prod.fst ≫ S.decidableVariables.test
  let m : V ⨯ (V ⨯ S.algebra.a.2) ⟶ Two D :=
    prod.lift prod.fst (prod.snd ≫ prod.snd ≫ S.formulaOccurrences) ≫
      S.lists.membership S.decidableVariables
  have hcap : S.identityQuantifierInput ≫ S.captureAllowed =
      Two.binary Bool.or (Two.unary Bool.not m) (Two.unary Bool.not b) :=
    S.identity_quantifier_capture
  apply Two.hom_ext b
  · let k := Two.fiberι b false
    have he : (k ≫ S.identityQuantifierInput) ≫ S.quantifierEquality =
        Two.constant (Two.Fiber b false) false := by
      rw [Category.assoc, S.identity_quantifier_equality]
      exact Two.fiberι_comp b false
    have hc : (k ≫ S.identityQuantifierInput) ≫ S.captureAllowed =
        Two.constant (Two.Fiber b false) true := by
      rw [Category.assoc, hcap, Two.comp_binary, Two.comp_unary, Two.comp_unary,
        Two.fiberι_comp, Two.unary_constant]
      exact sup_top_eq _
    have h := S.quantifierSubstitution_distinct_allowed (k ≫ S.identityQuantifierInput) he hc
    have h' : k ≫ S.identityQuantifierInput ≫ S.quantifierSubstitutionResult =
        prod.lift (k ≫ prod.snd ≫ prod.fst) (k ≫ prod.snd ≫ prod.snd ≫ coprod.inr) ≫
          OptionSyntax.coefficient S.quantifierConstructor := by
      simpa [identityQuantifierInput, identityPair, Category.assoc] using h
    have hok : prod.lift (k ≫ prod.snd ≫ prod.fst)
        (k ≫ prod.snd ≫ prod.snd ≫ coprod.inr) ≫
          OptionSyntax.coefficient S.quantifierConstructor =
        prod.lift (k ≫ prod.snd ≫ prod.fst) (k ≫ prod.snd ≫ prod.snd) ≫
          S.quantifierConstructor ≫ coprod.inr := by
      simpa only [Category.assoc] using OptionSyntax.coefficient_ok S.quantifierConstructor
        (k ≫ prod.snd ≫ prod.fst) (k ≫ prod.snd ≫ prod.snd)
    have h'' := h'.trans hok
    have hk : prod.lift (k ≫ prod.snd ≫ prod.fst) (k ≫ prod.snd ≫ prod.snd) =
        k ≫ prod.snd := by
      apply prod.hom_ext <;> simp only [prod.lift_fst, prod.lift_snd, Category.assoc]
    rw [hk] at h''
    simpa only [k, Category.assoc] using h''
  · let k := Two.fiberι b true
    have he : (k ≫ S.identityQuantifierInput) ≫ S.quantifierEquality =
        Two.constant (Two.Fiber b true) true := by
      rw [Category.assoc, S.identity_quantifier_equality]
      exact Two.fiberι_comp b true
    have h : (k ≫ S.identityQuantifierInput) ≫ S.quantifierSubstitutionResult =
        (k ≫ S.identityQuantifierInput) ≫ S.quantifierOriginal ≫ coprod.inr := by
      unfold quantifierSubstitutionResult
      simpa using Two.comp_branch _ _ _ (k ≫ S.identityQuantifierInput) true he
    simpa only [Category.assoc, S.identity_quantifier_original_assoc] using h

theorem quantifier_identity_pair :
    S.identityQuantifierInput ≫ S.quantifierSubstitutionPair =
      prod.snd ≫ S.quantifierConstructor ≫ S.identityPair.2 := by
  simp [quantifierSubstitutionPair, S.quantifier_identity_result, identityPair]

theorem identityCandidate_comparison (p : SyntaxPolynomial D) :
    polynomialMap S.identityParameters (A := S.parameterSyntaxFamilies V)
        S.identityCandidate p ≫
      SyntaxPolynomial.parameterComparison S.substitutionParameters S.substitutionCarriers p =
      (Over.map S.identityParameters).map (SyntaxPolynomial.parameterComparison V S.algebra.a p) ≫
        baseMap S.identityParameters (p.eval.obj S.algebra.a) ≫
          (constantFamilyFunctor S.substitutionParameters).map (p.eval.map S.identityPair) := by
  let f : ((Over.map S.identityParameters).obj (constantFamily V S.algebra.a.1),
      (Over.map S.identityParameters).obj (constantFamily V S.algebra.a.2)) ⟶
        (constantFamily S.substitutionParameters S.algebra.a.1,
          constantFamily S.substitutionParameters S.algebra.a.2) :=
    (baseMap S.identityParameters S.algebra.a.1,
      baseMap S.identityParameters S.algebra.a.2)
  let g : (constantFamily S.substitutionParameters S.algebra.a.1,
      constantFamily S.substitutionParameters S.algebra.a.2) ⟶
        (constantFamily S.substitutionParameters S.substitutionCarriers.1,
          constantFamily S.substitutionParameters S.substitutionCarriers.2) :=
    ((constantFamilyFunctor S.substitutionParameters).map S.identityPair.1,
      (constantFamilyFunctor S.substitutionParameters).map S.identityPair.2)
  have hfg : S.identityCandidate = f ≫ g := rfl
  rw [hfg]
  have hm := polynomialMap_right S.identityParameters
    (A := S.parameterSyntaxFamilies V) f g p
  have hn := SyntaxPolynomial.parameterComparison_natural
    S.substitutionParameters S.identityPair p
  calc
    polynomialMap S.identityParameters (A := S.parameterSyntaxFamilies V) (f ≫ g) p ≫
        SyntaxPolynomial.parameterComparison S.substitutionParameters S.substitutionCarriers p =
      polynomialMap S.identityParameters (A := S.parameterSyntaxFamilies V) f p ≫
        ((p.withParameters S.substitutionParameters).eval.map g ≫
          SyntaxPolynomial.parameterComparison S.substitutionParameters S.substitutionCarriers p) :=
        (congrArg (fun k => k ≫ SyntaxPolynomial.parameterComparison
          S.substitutionParameters S.substitutionCarriers p) hm).symm.trans
            (Category.assoc _ _ _)
    _ = polynomialMap S.identityParameters (A := S.parameterSyntaxFamilies V) f p ≫
        (SyntaxPolynomial.parameterComparison S.substitutionParameters S.algebra.a p ≫
          (constantFamilyFunctor S.substitutionParameters).map (p.eval.map S.identityPair)) :=
        congrArg (fun k => polynomialMap S.identityParameters (A := S.parameterSyntaxFamilies V) f p ≫ k) hn
    _ = _ := (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ (constantFamilyFunctor S.substitutionParameters).map
        (p.eval.map S.identityPair))
          (polynomialMap_comparison S.identityParameters S.algebra.a p)).trans
            (Category.assoc _ _ _))

theorem identity_operation (p : SyntaxPolynomial D) {Y Z : D}
    (α : p.eval.obj S.algebra.a ⟶ Y) (β : p.eval.obj S.substitutionCarriers ⟶ Z)
    (u : Y ⟶ Z) (h : p.eval.map S.identityPair ≫ β = α ≫ u) :
    polynomialMap S.identityParameters (A := S.parameterSyntaxFamilies V)
        S.identityCandidate p ≫
      (SyntaxPolynomial.parameterComparison S.substitutionParameters S.substitutionCarriers p ≫
        (constantFamilyFunctor S.substitutionParameters).map β) =
      (Over.map S.identityParameters).map (SyntaxPolynomial.parameterComparison V S.algebra.a p ≫
        (constantFamilyFunctor V).map α) ≫ baseMap S.identityParameters Y ≫
          (constantFamilyFunctor S.substitutionParameters).map u := by
  rw [← Category.assoc, S.identityCandidate_comparison]
  have hh : (constantFamilyFunctor S.substitutionParameters).map (p.eval.map S.identityPair) ≫
      (constantFamilyFunctor S.substitutionParameters).map β =
      (constantFamilyFunctor S.substitutionParameters).map α ≫
        (constantFamilyFunctor S.substitutionParameters).map u := by
    rw [← (constantFamilyFunctor S.substitutionParameters).map_comp, h,
      (constantFamilyFunctor S.substitutionParameters).map_comp]
  calc
    _ = (Over.map S.identityParameters).map
        (SyntaxPolynomial.parameterComparison V S.algebra.a p) ≫
      baseMap S.identityParameters (p.eval.obj S.algebra.a) ≫
        ((constantFamilyFunctor S.substitutionParameters).map (p.eval.map S.identityPair) ≫
          (constantFamilyFunctor S.substitutionParameters).map β) := by
            simp only [Category.assoc]
    _ = (Over.map S.identityParameters).map
        (SyntaxPolynomial.parameterComparison V S.algebra.a p) ≫
      (baseMap S.identityParameters (p.eval.obj S.algebra.a) ≫
        (constantFamilyFunctor S.substitutionParameters).map α) ≫
          (constantFamilyFunctor S.substitutionParameters).map u := by
            rw [hh, Category.assoc]
    _ = _ := by
      rw [baseMap_natural]
      simp only [(Over.map S.identityParameters).map_comp, Category.assoc]

theorem variable_identity_cross :
    baseMap S.identityParameters V ≫ parameterHom S.variableSubstitutionPair =
      (Over.map S.identityParameters).map ((constantFamilyFunctor V).map S.variableConstructor) ≫
        S.identityCandidate.1 := by
  apply Over.OverMorphism.ext
  apply prod.hom_ext
  · exact (Over.w _).trans (Over.w _).symm
  · simpa [baseMap, constantFamilyFunctor, Over.map, parameterHom,
      identityCandidate, identityPair, identityParameters] using S.variable_identity_pair

theorem quantifier_identity_cross :
    baseMap S.identityParameters (V ⨯ S.algebra.a.2) ≫
        (constantFamilyFunctor S.substitutionParameters).map
          (prod.map (𝟙 V) S.identityPair.2) ≫ parameterHom S.quantifierSubstitutionPair =
      (Over.map S.identityParameters).map ((constantFamilyFunctor V).map S.quantifierConstructor) ≫
        S.identityCandidate.2 := by
  have hi : prod.map S.identityParameters (prod.map (𝟙 V) S.identityPair.2) =
      S.identityQuantifierInput := by
    apply prod.hom_ext
    · simp [identityQuantifierInput]
    · apply prod.hom_ext <;> simp [identityQuantifierInput]
  have h := S.quantifier_identity_pair
  rw [← hi] at h
  apply Over.OverMorphism.ext
  apply prod.hom_ext
  · exact (Over.w _).trans (Over.w _).symm
  · simpa [baseMap, constantFamilyFunctor, Over.map, parameterHom, identityCandidate,
      identityPair, identityParameters] using h

theorem quantifier_identity_operation :
    polynomialMap S.identityParameters (A := S.parameterSyntaxFamilies V)
        S.identityCandidate (.product (.coefficient V) .formula) ≫
      (SyntaxPolynomial.parameterComparison S.substitutionParameters S.substitutionCarriers
        (.product (.coefficient V) .formula) ≫ parameterHom S.quantifierSubstitutionPair) =
      (Over.map S.identityParameters).map
          (SyntaxPolynomial.parameterComparison V S.algebra.a
            (.product (.coefficient V) .formula) ≫
              (constantFamilyFunctor V).map S.quantifierConstructor) ≫
        S.identityCandidate.2 := by
  rw [← Category.assoc, S.identityCandidate_comparison]
  simp only [Category.assoc]
  change (Over.map S.identityParameters).map
      (SyntaxPolynomial.parameterComparison V S.algebra.a
        (.product (.coefficient V) .formula)) ≫
    baseMap S.identityParameters (V ⨯ S.algebra.a.2) ≫
      (constantFamilyFunctor S.substitutionParameters).map (prod.map (𝟙 V) S.identityPair.2) ≫
        parameterHom S.quantifierSubstitutionPair = _
  rw [S.quantifier_identity_cross, ← (Over.map S.identityParameters).map_comp_assoc]

theorem term_parameter_structure (R : D) :
    (SyntaxPolynomial.algebraWithParameters (SyntaxPolynomial.termExpression V σ d)
      (SyntaxPolynomial.formulaExpression V π d) S.algebra R).str.1 =
      coprod.desc ((constantFamilyFunctor R).map S.variableConstructor)
        (SyntaxPolynomial.parameterComparison R S.algebra.a (SyntaxPolynomial.constructors σ d) ≫
          (constantFamilyFunctor R).map S.functionConstructors) := by
  change SyntaxPolynomial.parameterComparison R S.algebra.a
      (.sum (.coefficient V) (SyntaxPolynomial.constructors σ d)) ≫
        (constantFamilyFunctor R).map S.algebra.str.1 = _
  apply coprod.hom_ext
  · rw [SyntaxPolynomial.parameterComparison_inl_assoc, coprod.inl_desc]
    simp only [SyntaxPolynomial.parameterComparison, Category.id_comp,
      ← (constantFamilyFunctor R).map_comp]
    rfl
  · rw [SyntaxPolynomial.parameterComparison_inr_assoc, coprod.inr_desc]
    simp only [← (constantFamilyFunctor R).map_comp]
    rfl

theorem formula_parameter_structure (R : D) :
    (SyntaxPolynomial.algebraWithParameters (SyntaxPolynomial.termExpression V σ d)
      (SyntaxPolynomial.formulaExpression V π d) S.algebra R).str.2 =
      coprod.desc
        (coprod.desc
          (coprod.desc
            (coprod.desc
              (SyntaxPolynomial.parameterComparison R S.algebra.a
                (SyntaxPolynomial.power .term 2) ≫
                  (constantFamilyFunctor R).map S.equalityConstructor)
              (SyntaxPolynomial.parameterComparison R S.algebra.a
                (SyntaxPolynomial.constructors π d) ≫
                  (constantFamilyFunctor R).map S.relationConstructors))
            ((constantFamilyFunctor R).map S.negationConstructor))
          (SyntaxPolynomial.parameterComparison R S.algebra.a
            (SyntaxPolynomial.power .formula 2) ≫
              (constantFamilyFunctor R).map S.implicationConstructor))
        (SyntaxPolynomial.parameterComparison R S.algebra.a
          (.product (.coefficient V) .formula) ≫
            (constantFamilyFunctor R).map S.quantifierConstructor) := by
  change SyntaxPolynomial.parameterComparison R S.algebra.a
      (.sum (.sum (.sum (.sum (SyntaxPolynomial.power .term 2)
        (SyntaxPolynomial.constructors π d)) .formula)
          (SyntaxPolynomial.power .formula 2)) (.product (.coefficient V) .formula)) ≫
      (constantFamilyFunctor R).map S.algebra.str.2 = _
  repeat' apply coprod.hom_ext
  all_goals
    simp only [SyntaxPolynomial.parameterComparison_inl_assoc,
      SyntaxPolynomial.parameterComparison_inr_assoc, coprod.inl_desc, coprod.inr_desc,
      ← (constantFamilyFunctor R).map_comp]
  all_goals try rfl
  all_goals simp only [SyntaxPolynomial.parameterComparison, Category.id_comp,
    negationConstructor, negationInjection, Category.assoc]
  all_goals rfl

theorem identityCandidate_eq_fold :
    S.identityCandidate = S.crossParameterFold S.identityParameters S.substitutionAlgebra := by
  refine S.crossParameterFold_unique S.identityParameters S.substitutionAlgebra
    S.identityCandidate ?_
  apply Prod.ext
  · rw [S.term_parameter_structure V]
    dsimp only [substitutionAlgebra, SyntaxPolynomial.termExpression]
    apply push_coprod_hom_ext S.identityParameters
    · simp only [polynomialMap_inl_assoc, coprod.inl_desc, map_inl_desc_assoc]
      exact S.variable_identity_cross
    · simpa only [polynomialMap_inr_assoc, coprod.inr_desc, coprod.inr_desc_assoc,
        map_inr_desc_assoc, S.identityCandidate_term, Category.assoc] using
        S.identity_operation (SyntaxPolynomial.constructors σ d) S.functionConstructors
          S.functionSubstitutionPair S.identityPair.1 S.function_identity_pair
  · rw [S.formula_parameter_structure V]
    dsimp only [substitutionAlgebra, SyntaxPolynomial.formulaExpression]
    apply push_coprod_hom_ext S.identityParameters
    · apply push_coprod_hom_ext S.identityParameters
      · apply push_coprod_hom_ext S.identityParameters
        · apply push_coprod_hom_ext S.identityParameters
          · simpa only [polynomialMap_inl_assoc, coprod.inl_desc, coprod.inl_desc_assoc,
              map_inl_desc_assoc, S.identityCandidate_formula, Category.assoc] using
              S.identity_operation (SyntaxPolynomial.power .term 2) S.equalityConstructor
                S.equalitySubstitutionPair S.identityPair.2 S.equality_identity_pair
          · simpa only [polynomialMap_inl_assoc, polynomialMap_inr_assoc,
              coprod.inl_desc, coprod.inr_desc, coprod.inl_desc_assoc, coprod.inr_desc_assoc,
              map_inl_desc_assoc, map_inr_desc_assoc, S.identityCandidate_formula,
              Category.assoc] using
              S.identity_operation (SyntaxPolynomial.constructors π d) S.relationConstructors
                S.relationSubstitutionPair S.identityPair.2 S.relation_identity_pair
        · simp only [polynomialMap_inl_assoc, polynomialMap_inr_assoc,
            coprod.inl_desc, coprod.inr_desc, map_inl_desc_assoc, map_inr_desc_assoc]
          change S.identityCandidate.2 ≫
            (constantFamilyFunctor S.substitutionParameters).map S.negationSubstitutionPair =
              (Over.map S.identityParameters).map
                ((constantFamilyFunctor V).map S.negationConstructor) ≫ S.identityCandidate.2
          have hn := S.identity_operation .formula S.negationConstructor
            S.negationSubstitutionPair S.identityPair.2 S.negation_identity_pair
          have he : SyntaxPolynomial.parameterComparison S.substitutionParameters
                S.substitutionCarriers .formula ≫
                  (constantFamilyFunctor S.substitutionParameters).map S.negationSubstitutionPair =
              (constantFamilyFunctor S.substitutionParameters).map S.negationSubstitutionPair :=
            Category.id_comp _
          have hv : SyntaxPolynomial.parameterComparison V S.algebra.a .formula ≫
                (constantFamilyFunctor V).map S.negationConstructor =
              (constantFamilyFunctor V).map S.negationConstructor := Category.id_comp _
          rw [he, hv] at hn
          exact hn

      · simpa only [polynomialMap_inl_assoc, polynomialMap_inr_assoc,
          coprod.inl_desc, coprod.inr_desc, coprod.inl_desc_assoc, coprod.inr_desc_assoc,
          map_inl_desc_assoc, map_inr_desc_assoc, S.identityCandidate_formula,
          Category.assoc] using
          S.identity_operation (SyntaxPolynomial.power .formula 2) S.implicationConstructor
            S.implicationSubstitutionPair S.identityPair.2 S.implication_identity_pair
    · simpa only [polynomialMap_inr_assoc, coprod.inr_desc, coprod.inr_desc_assoc,
        map_inr_desc_assoc, Category.assoc] using S.quantifier_identity_operation

theorem identity_fold_term_result :
    prod.map S.identityParameters (𝟙 S.algebra.a.1) ≫ S.substitutionFold.1.left ≫
      prod.snd ≫ prod.snd = prod.snd := by
  have hc : S.identityCandidate.1.left ≫ prod.snd ≫ prod.snd = prod.snd := by
    change (prod.map S.identityParameters (𝟙 S.algebra.a.1) ≫
      prod.map (𝟙 S.substitutionParameters)
        (prod.lift (𝟙 S.algebra.a.1) (𝟙 S.algebra.a.1))) ≫
          prod.snd ≫ prod.snd = prod.snd
    simp only [Category.assoc, prod.map_snd_assoc, prod.map_snd, prod.lift_snd,
      Category.comp_id]
  have h := congrArg (fun f => f.1.left ≫ prod.snd ≫ prod.snd) S.identityCandidate_eq_fold
  change S.identityCandidate.1.left ≫ prod.snd ≫ prod.snd =
    (prod.map S.identityParameters (𝟙 S.algebra.a.1) ≫ S.substitutionFold.1.left) ≫
      prod.snd ≫ prod.snd at h
  simp only [Category.assoc] at h
  exact h.symm.trans hc

theorem identity_fold_formula_result :
    prod.map S.identityParameters (𝟙 S.algebra.a.2) ≫ S.substitutionFold.2.left ≫
      prod.snd ≫ prod.snd = prod.snd ≫ coprod.inr := by
  have hc : S.identityCandidate.2.left ≫ prod.snd ≫ prod.snd =
      prod.snd ≫ coprod.inr := by
    change (prod.map S.identityParameters (𝟙 S.algebra.a.2) ≫
      prod.map (𝟙 S.substitutionParameters)
        (prod.lift (𝟙 S.algebra.a.2) coprod.inr)) ≫
          prod.snd ≫ prod.snd = prod.snd ≫ coprod.inr
    simp only [Category.assoc, prod.map_snd_assoc, prod.lift_snd, Category.id_comp]
  have h := congrArg (fun f => f.2.left ≫ prod.snd ≫ prod.snd) S.identityCandidate_eq_fold
  change S.identityCandidate.2.left ≫ prod.snd ≫ prod.snd =
    (prod.map S.identityParameters (𝟙 S.algebra.a.2) ≫ S.substitutionFold.2.left) ≫
      prod.snd ≫ prod.snd at h
  simp only [Category.assoc] at h
  exact h.symm.trans hc

def identityTermInput : S.algebra.a.1 ⨯ V ⟶ S.algebra.a.1 ⨯ S.substitutionParameters :=
  prod.map (𝟙 _) S.identityParameters

def identityFormulaInput : S.algebra.a.2 ⨯ V ⟶ S.algebra.a.2 ⨯ S.substitutionParameters :=
  prod.map (𝟙 _) S.identityParameters

/-- Substitution of a named variable by its own variable term fixes every term. -/
theorem term_substitution_identity :
    S.identityTermInput ≫ S.termSubstitution = prod.fst := by
  unfold identityTermInput termSubstitution
  rw [← Category.assoc, braid_natural]
  simp only [Category.assoc, S.identity_fold_term_result, prod.braiding_hom, prod.lift_snd]

/-- Identity substitution succeeds on every formula and fixes it. -/
theorem formula_substitution_identity :
    S.identityFormulaInput ≫ S.formulaSubstitutionOption = prod.fst ≫ coprod.inr := by
  unfold identityFormulaInput formulaSubstitutionOption
  rw [← Category.assoc, braid_natural]
  simp only [Category.assoc, S.identity_fold_formula_result, prod.braiding_hom, prod.lift_snd_assoc]

def identityFormulaAdmissible : S.algebra.a.2 ⨯ V ⟶ S.admissibleSubstitution :=
  pullback.lift S.identityFormulaInput prod.fst S.formula_substitution_identity

@[simp, reassoc] theorem identityFormulaAdmissible_inclusion :
    S.identityFormulaAdmissible ≫ S.admissibleInclusion = S.identityFormulaInput :=
  pullback.lift_fst _ _ _

@[simp, reassoc] theorem identityFormulaAdmissible_substitution :
    S.identityFormulaAdmissible ≫ S.formulaSubstitution = prod.fst :=
  pullback.lift_snd _ _ _

end CategoricalEssentialIncompleteness.V46.CategoricalSyntax
