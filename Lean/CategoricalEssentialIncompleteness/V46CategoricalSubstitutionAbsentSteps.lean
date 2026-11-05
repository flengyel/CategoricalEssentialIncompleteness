import CategoricalEssentialIncompleteness.V46CategoricalSubstitutionAbsentInvariant

/-! Constructor calculations for substitution at an absent named variable. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.CategoricalSyntax
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V : D} {σ π : ℕ → D} {d : ℕ} (S : CategoricalSyntax V σ π d)
attribute [local simp] prod.comp_lift_assoc prod.lift_fst_assoc prod.lift_snd_assoc
  prod.map_fst_assoc prod.map_snd_assoc

def termAbsenceTest {X : D} (p : X ⟶ S.substitutionParameters) (u : X ⟶ S.algebra.a.1) :
    X ⟶ Two D := prod.lift (p ≫ prod.fst) (u ≫ S.termOccurrences) ≫
  S.lists.membership S.decidableVariables

def formulaAbsenceTest {X : D} (p : X ⟶ S.substitutionParameters) (φ : X ⟶ S.algebra.a.2) :
    X ⟶ Two D := prod.lift (p ≫ prod.fst) (φ ≫ S.formulaOccurrences) ≫
  S.lists.membership S.decidableVariables

@[simp] theorem termAbsenceTest_comp {X Y : D} (k : X ⟶ Y)
    (p : Y ⟶ S.substitutionParameters) (u : Y ⟶ S.algebra.a.1) :
    k ≫ S.termAbsenceTest p u = S.termAbsenceTest (k ≫ p) (k ≫ u) := by
  simp [termAbsenceTest, Category.assoc]

@[simp] theorem formulaAbsenceTest_comp {X Y : D} (k : X ⟶ Y)
    (p : Y ⟶ S.substitutionParameters) (φ : Y ⟶ S.algebra.a.2) :
    k ≫ S.formulaAbsenceTest p φ = S.formulaAbsenceTest (k ≫ p) (k ≫ φ) := by
  simp [formulaAbsenceTest, Category.assoc]

def termPairGood {X : D} (p : X ⟶ S.substitutionParameters)
    (a : X ⟶ S.substitutionCarriers.1) : Prop :=
  ConditionalInvariant.Holds (S.termAbsenceTest p (a ≫ prod.fst))
    (a ≫ prod.fst) (a ≫ prod.snd)

def formulaPairGood {X : D} (p : X ⟶ S.substitutionParameters)
    (a : X ⟶ S.substitutionCarriers.2) : Prop :=
  ConditionalInvariant.Holds (S.formulaAbsenceTest p (a ≫ prod.fst))
    (a ≫ prod.fst ≫ coprod.inr) (a ≫ prod.snd)

theorem termPairGood_comp {X Y : D} (p : Y ⟶ S.substitutionParameters)
    (a : Y ⟶ S.substitutionCarriers.1) (h : S.termPairGood p a) (k : X ⟶ Y) :
    S.termPairGood (k ≫ p) (k ≫ a) := by
  simpa only [termPairGood, S.termAbsenceTest_comp, Category.assoc] using
    ConditionalInvariant.precomp h k

theorem formulaPairGood_comp {X Y : D} (p : Y ⟶ S.substitutionParameters)
    (a : Y ⟶ S.substitutionCarriers.2) (h : S.formulaPairGood p a) (k : X ⟶ Y) :
    S.formulaPairGood (k ≫ p) (k ≫ a) := by
  simpa only [formulaPairGood, S.formulaAbsenceTest_comp, Category.assoc] using
    ConditionalInvariant.precomp h k

theorem termPair_fixed {X Y : D} (p : Y ⟶ S.substitutionParameters)
    (a : Y ⟶ S.substitutionCarriers.1) (h : S.termPairGood p a) (k : X ⟶ Y)
    (ha : S.termAbsenceTest (k ≫ p) (k ≫ a ≫ prod.fst) = Two.constant X false) :
    k ≫ a ≫ prod.snd = k ≫ a ≫ prod.fst := by
  apply ConditionalInvariant.fixed_of_false h k
  simpa only [S.termAbsenceTest_comp, Category.assoc] using ha

theorem formulaPair_fixed {X Y : D} (p : Y ⟶ S.substitutionParameters)
    (a : Y ⟶ S.substitutionCarriers.2) (h : S.formulaPairGood p a) (k : X ⟶ Y)
    (ha : S.formulaAbsenceTest (k ≫ p) (k ≫ a ≫ prod.fst) = Two.constant X false) :
    k ≫ a ≫ prod.snd = k ≫ a ≫ prod.fst ≫ coprod.inr := by
  apply ConditionalInvariant.fixed_of_false h k
  simpa only [S.formulaAbsenceTest_comp, Category.assoc] using ha

theorem termPairGood_of_fixed {X : D} (p : X ⟶ S.substitutionParameters)
    (a : X ⟶ S.substitutionCarriers.1)
    (h : ∀ {Y : D} (k : Y ⟶ X),
      S.termAbsenceTest (k ≫ p) (k ≫ a ≫ prod.fst) = Two.constant Y false →
        k ≫ a ≫ prod.snd = k ≫ a ≫ prod.fst) : S.termPairGood p a := by
  apply ConditionalInvariant.holds_of_false_fiber
  let b := S.termAbsenceTest p (a ≫ prod.fst)
  exact h (Two.fiberι b false) (by
    simpa only [b, S.termAbsenceTest_comp, Category.assoc] using Two.fiberι_comp b false)

theorem formulaPairGood_of_fixed {X : D} (p : X ⟶ S.substitutionParameters)
    (a : X ⟶ S.substitutionCarriers.2)
    (h : ∀ {Y : D} (k : Y ⟶ X),
      S.formulaAbsenceTest (k ≫ p) (k ≫ a ≫ prod.fst) = Two.constant Y false →
        k ≫ a ≫ prod.snd = k ≫ a ≫ prod.fst ≫ coprod.inr) : S.formulaPairGood p a := by
  apply ConditionalInvariant.holds_of_false_fiber
  let b := S.formulaAbsenceTest p (a ≫ prod.fst)
  exact h (Two.fiberι b false) (by
    simpa only [b, S.formulaAbsenceTest_comp, Category.assoc] using Two.fiberι_comp b false)

theorem append_absence {X : D} (x : X ⟶ V)
    (w w' : X ⟶ S.lists.algebra.carrier)
    (h : prod.lift x (prod.lift w w' ≫ S.lists.append) ≫
      S.lists.membership S.decidableVariables = Two.constant X false) :
    prod.lift x w ≫ S.lists.membership S.decidableVariables = Two.constant X false ∧
      prod.lift x w' ≫ S.lists.membership S.decidableVariables = Two.constant X false := by
  rw [S.lists.membership_append] at h
  change (prod.lift x w ≫ S.lists.membership S.decidableVariables) ⊔
    (prod.lift x w' ≫ S.lists.membership S.decidableVariables) = ⊥ at h
  exact ⟨bot_unique (le_trans le_sup_left h.le), bot_unique (le_trans le_sup_right h.le)⟩

theorem equality_absent_value {X : D} (p : X ⟶ S.substitutionParameters)
    (a b : X ⟶ S.substitutionCarriers.1)
    (ga : S.termPairGood p a) (gb : S.termPairGood p b)
    (ha : S.formulaAbsenceTest p
      (prod.lift (a ≫ prod.fst) (b ≫ prod.fst) ≫ S.equalityConstructor) =
        Two.constant X false) :
    prod.lift a b ≫ S.equalitySubstitutionPair ≫ prod.snd =
      prod.lift (a ≫ prod.fst) (b ≫ prod.fst) ≫ S.equalityConstructor ≫ coprod.inr := by
  have hFV : prod.lift (p ≫ prod.fst)
      (prod.lift (a ≫ prod.fst ≫ S.termOccurrences) (b ≫ prod.fst ≫ S.termOccurrences) ≫
        S.lists.append) ≫ S.lists.membership S.decidableVariables =
          Two.constant X false := by
    simpa only [formulaAbsenceTest, S.equality_occurrences, Category.assoc,
      prod.lift_map_assoc] using ha
  have hab := S.append_absence (p ≫ prod.fst) _ _ hFV
  have ha' := S.termPair_fixed p a ga (𝟙 X) (by
    simpa only [Category.id_comp, termAbsenceTest, Category.assoc] using hab.1)
  have hb' := S.termPair_fixed p b gb (𝟙 X) (by
    simpa only [Category.id_comp, termAbsenceTest, Category.assoc] using hab.2)
  simp only [Category.id_comp] at ha' hb'
  simp [equalitySubstitutionPair, SyntaxPolynomial.power, SyntaxPolynomial.eval,
    SyntaxPolynomial.productFunctor, termResultProjection, ha', hb']

theorem negation_absent_value {X : D} (p : X ⟶ S.substitutionParameters)
    (a : X ⟶ S.substitutionCarriers.2) (good : S.formulaPairGood p a)
    (ha : S.formulaAbsenceTest p (a ≫ prod.fst ≫ S.negationConstructor) =
      Two.constant X false) :
    a ≫ S.negationSubstitutionPair ≫ prod.snd =
      a ≫ prod.fst ≫ S.negationConstructor ≫ coprod.inr := by
  have habody : S.formulaAbsenceTest p (a ≫ prod.fst) = Two.constant X false := by
    simpa only [formulaAbsenceTest, S.negation_occurrences, Category.assoc] using ha
  have hbody := S.formulaPair_fixed p a good (𝟙 X) (by
    simpa only [Category.id_comp] using habody)
  simp only [Category.id_comp] at hbody
  simp only [negationSubstitutionPair, prod.lift_snd]
  calc
    _ = (a ≫ prod.snd) ≫ OptionSyntax.map S.negationConstructor := (Category.assoc _ _ _).symm
    _ = (a ≫ prod.fst ≫ coprod.inr) ≫ OptionSyntax.map S.negationConstructor :=
      congrArg (fun f => f ≫ OptionSyntax.map S.negationConstructor) hbody
    _ = _ := by simp only [Category.assoc, OptionSyntax.map_ok]

theorem implication_absent_value {X : D} (p : X ⟶ S.substitutionParameters)
    (a b : X ⟶ S.substitutionCarriers.2)
    (ga : S.formulaPairGood p a) (gb : S.formulaPairGood p b)
    (ha : S.formulaAbsenceTest p
      (prod.lift (a ≫ prod.fst) (b ≫ prod.fst) ≫ S.implicationConstructor) =
        Two.constant X false) :
    prod.lift a b ≫ S.implicationSubstitutionPair ≫ prod.snd =
      prod.lift (a ≫ prod.fst) (b ≫ prod.fst) ≫ S.implicationConstructor ≫ coprod.inr := by
  have hFV : prod.lift (p ≫ prod.fst)
      (prod.lift (a ≫ prod.fst ≫ S.formulaOccurrences)
        (b ≫ prod.fst ≫ S.formulaOccurrences) ≫ S.lists.append) ≫
          S.lists.membership S.decidableVariables = Two.constant X false := by
    simpa only [formulaAbsenceTest, S.implication_occurrences, Category.assoc,
      prod.lift_map_assoc] using ha
  have hab := S.append_absence (p ≫ prod.fst) _ _ hFV
  have ha' := S.formulaPair_fixed p a ga (𝟙 X) (by
    simpa only [Category.id_comp, formulaAbsenceTest, Category.assoc] using hab.1)
  have hb' := S.formulaPair_fixed p b gb (𝟙 X) (by
    simpa only [Category.id_comp, formulaAbsenceTest, Category.assoc] using hab.2)
  simp only [Category.id_comp] at ha' hb'
  have hstep : prod.lift a b ≫ S.implicationSubstitutionPair ≫ prod.snd =
      prod.lift (a ≫ prod.snd) (b ≫ prod.snd) ≫
        OptionSyntax.binary S.implicationConstructor := by
    simp [implicationSubstitutionPair]
  rw [hstep, ha', hb']
  simpa only [Category.assoc] using
    OptionSyntax.binary_ok S.implicationConstructor (a ≫ prod.fst) (b ≫ prod.fst)

/-- Distinct quantifier and substitution names transfer absence through deletion. -/
theorem quantified_body_absent {X : D} (p : X ⟶ S.substitutionParameters)
    (y : X ⟶ V) (φ : X ⟶ S.algebra.a.2)
    (he : prod.lift y (p ≫ prod.fst) ≫ S.decidableVariables.test = Two.constant X false)
    (ha : S.formulaAbsenceTest p (prod.lift y φ ≫ S.quantifierConstructor) =
      Two.constant X false) : S.formulaAbsenceTest p φ = Two.constant X false := by
  unfold formulaAbsenceTest at ha ⊢
  simp only [Category.assoc] at ha
  rw [S.quantifier_membership, S.decidableVariables.test_reverse, he,
    Two.unary_constant] at ha
  exact (top_inf_eq _).symm.trans ha

theorem variable_absent_value {X : D} (p : X ⟶ S.substitutionParameters) (y : X ⟶ V)
    (ha : S.termAbsenceTest p (y ≫ S.variableConstructor) = Two.constant X false) :
    prod.lift p y ≫ S.variableSubstitutionPair ≫ prod.snd = y ≫ S.variableConstructor := by
  have he : prod.lift y (p ≫ prod.fst) ≫ S.decidableVariables.test =
      Two.constant X false := by
    rw [S.decidableVariables.test_reverse]
    simpa only [termAbsenceTest, Category.assoc, S.variable_membership] using ha
  have hb : prod.lift p y ≫
      (prod.lift prod.snd (prod.fst ≫ prod.fst) ≫ S.decidableVariables.test) =
        Two.constant X false := by
    simpa only [prod.comp_lift_assoc, prod.lift_snd, prod.lift_fst_assoc] using he
  unfold variableSubstitutionPair
  rw [prod.lift_snd, Two.comp_branch _ _ _ _ false hb]
  simp

/-- Absence from the original quantified body makes the capture test true,
for an arbitrary replacement term. -/
theorem capture_allowed_of_body_absent {X : D} (p : X ⟶ S.substitutionParameters)
    (y : X ⟶ V) (a : X ⟶ S.substitutionCarriers.2)
    (ha : S.formulaAbsenceTest p (a ≫ prod.fst) = Two.constant X false) :
    prod.lift p (prod.lift y a) ≫ S.captureAllowed = Two.constant X true := by
  have h : prod.lift p (prod.lift y a) ≫ S.captureAllowed =
      Two.binary Bool.or (Two.unary Bool.not (S.formulaAbsenceTest p (a ≫ prod.fst)))
        (Two.unary Bool.not (prod.lift y (p ≫ prod.snd ≫ S.termOccurrences) ≫
          S.lists.membership S.decidableVariables)) := by
    simp [captureAllowed, formulaAbsenceTest]
  rw [h, ha, Two.unary_constant]
  exact top_sup_eq _

/-- The actual quantifier operation fixes an absent-variable input under the
recursive invariant; equal-name binding bypasses the recursive result. -/
theorem quantifier_absent_value {X : D} (p : X ⟶ S.substitutionParameters)
    (y : X ⟶ V) (a : X ⟶ S.substitutionCarriers.2)
    (good : S.formulaPairGood p a)
    (ha : S.formulaAbsenceTest p
      (prod.lift y (a ≫ prod.fst) ≫ S.quantifierConstructor) = Two.constant X false) :
    prod.lift p (prod.lift y a) ≫ S.quantifierSubstitutionResult =
      prod.lift y (a ≫ prod.fst) ≫ S.quantifierConstructor ≫ coprod.inr := by
  let input := prod.lift p (prod.lift y a)
  let b := prod.lift y (p ≫ prod.fst) ≫ S.decidableVariables.test
  have heq : input ≫ S.quantifierEquality = b := by simp [input, b, quantifierEquality]
  have horig : input ≫ S.quantifierOriginal =
      prod.lift y (a ≫ prod.fst) ≫ S.quantifierConstructor := by
    simp [input, quantifierOriginal]
  apply Two.hom_ext b
  · let k := Two.fiberι b false
    have he : (k ≫ input) ≫ S.quantifierEquality = Two.constant (Two.Fiber b false) false := by
      rw [Category.assoc, heq]
      exact Two.fiberι_comp b false
    have hname : prod.lift (k ≫ y) (k ≫ p ≫ prod.fst) ≫ S.decidableVariables.test =
        Two.constant (Two.Fiber b false) false := by
      simpa only [b, prod.comp_lift_assoc, Category.assoc] using Two.fiberι_comp b false
    have habody := S.quantified_body_absent (k ≫ p) (k ≫ y) (k ≫ a ≫ prod.fst) (by simpa only [Category.assoc] using hname)
      (by simpa only [S.formulaAbsenceTest_comp, prod.comp_lift_assoc, Category.assoc, Two.comp_constant]
        using congrArg (fun h => k ≫ h) ha)
    have hc : (k ≫ input) ≫ S.captureAllowed = Two.constant (Two.Fiber b false) true := by
      simpa only [input, prod.comp_lift, Category.assoc] using
        S.capture_allowed_of_body_absent (k ≫ p) (k ≫ y) (k ≫ a)
          (by simpa only [Category.assoc] using habody)
    have hbody := S.formulaPair_fixed p a good k habody
    have hstep := S.quantifierSubstitution_distinct_allowed (k ≫ input) he hc
    have hstep' : k ≫ input ≫ S.quantifierSubstitutionResult =
        prod.lift (k ≫ y) (k ≫ a ≫ prod.snd) ≫
          OptionSyntax.coefficient S.quantifierConstructor := by
      simpa [input, Category.assoc] using hstep
    rw [hbody] at hstep'
    have hok : prod.lift (k ≫ y) (k ≫ a ≫ prod.fst ≫ coprod.inr) ≫
        OptionSyntax.coefficient S.quantifierConstructor =
      prod.lift (k ≫ y) (k ≫ a ≫ prod.fst) ≫ S.quantifierConstructor ≫ coprod.inr := by
      simpa only [Category.assoc] using OptionSyntax.coefficient_ok S.quantifierConstructor
        (k ≫ y) (k ≫ a ≫ prod.fst)
    simpa only [input, prod.comp_lift_assoc, Category.assoc] using hstep'.trans hok
  · let k := Two.fiberι b true
    have he : (k ≫ input) ≫ S.quantifierEquality = Two.constant (Two.Fiber b true) true := by
      rw [Category.assoc, heq]
      exact Two.fiberι_comp b true
    have hr : (k ≫ input) ≫ S.quantifierSubstitutionResult =
        (k ≫ input) ≫ S.quantifierOriginal ≫ coprod.inr := by
      unfold quantifierSubstitutionResult
      exact Two.comp_branch _ _ _ _ true he
    simp only [Category.assoc] at hr
    have ho := congrArg (fun f => k ≫ f ≫
      (coprod.inr : S.algebra.a.2 ⟶ OptionSyntax.obj S.algebra.a.2)) horig
    simp only [Category.assoc] at ho
    simpa only [k, input, Category.assoc] using hr.trans ho

theorem variable_pair_good {X : D} (p : X ⟶ S.substitutionParameters) (y : X ⟶ V) :
    S.termPairGood p (prod.lift p y ≫ S.variableSubstitutionPair) := by
  apply S.termPairGood_of_fixed
  intro Y k ha
  have ha' : S.termAbsenceTest (k ≫ p) (k ≫ y ≫ S.variableConstructor) =
      Two.constant Y false := by
    simpa [variableSubstitutionPair, Category.assoc] using ha
  simpa [variableSubstitutionPair, prod.comp_lift_assoc, Category.assoc] using
    S.variable_absent_value (k ≫ p) (k ≫ y) (by simpa only [Category.assoc] using ha')

theorem equality_pair_good {X : D} (p : X ⟶ S.substitutionParameters)
    (a b : X ⟶ S.substitutionCarriers.1)
    (ga : S.termPairGood p a) (gb : S.termPairGood p b) :
    S.formulaPairGood p (prod.lift a b ≫ S.equalitySubstitutionPair) := by
  apply S.formulaPairGood_of_fixed
  intro Y k ha
  have ha' : S.formulaAbsenceTest (k ≫ p)
      (prod.lift (k ≫ a ≫ prod.fst) (k ≫ b ≫ prod.fst) ≫ S.equalityConstructor) =
        Two.constant Y false := by
    simpa [equalitySubstitutionPair, originalProjection, SyntaxPolynomial.power,
      SyntaxPolynomial.eval, SyntaxPolynomial.productFunctor, prod.lift_map,
      Category.assoc] using ha
  simpa [equalitySubstitutionPair, originalProjection, SyntaxPolynomial.power,
    SyntaxPolynomial.eval, SyntaxPolynomial.productFunctor, prod.lift_map,
    prod.comp_lift_assoc, Category.assoc] using
    S.equality_absent_value (k ≫ p) (k ≫ a) (k ≫ b)
      (S.termPairGood_comp p a ga k) (S.termPairGood_comp p b gb k)
      (by simpa only [Category.assoc] using ha')

theorem negation_pair_good {X : D} (p : X ⟶ S.substitutionParameters)
    (a : X ⟶ S.substitutionCarriers.2) (good : S.formulaPairGood p a) :
    S.formulaPairGood p (a ≫ S.negationSubstitutionPair) := by
  apply S.formulaPairGood_of_fixed
  intro Y k ha
  have ha' : S.formulaAbsenceTest (k ≫ p) (k ≫ a ≫ prod.fst ≫ S.negationConstructor) =
      Two.constant Y false := by
    simpa [negationSubstitutionPair, Category.assoc] using ha
  simpa [negationSubstitutionPair, Category.assoc] using
    S.negation_absent_value (k ≫ p) (k ≫ a) (S.formulaPairGood_comp p a good k) (by simpa only [Category.assoc] using ha')

theorem implication_pair_good {X : D} (p : X ⟶ S.substitutionParameters)
    (a b : X ⟶ S.substitutionCarriers.2)
    (ga : S.formulaPairGood p a) (gb : S.formulaPairGood p b) :
    S.formulaPairGood p (prod.lift a b ≫ S.implicationSubstitutionPair) := by
  apply S.formulaPairGood_of_fixed
  intro Y k ha
  have ha' : S.formulaAbsenceTest (k ≫ p)
      (prod.lift (k ≫ a ≫ prod.fst) (k ≫ b ≫ prod.fst) ≫ S.implicationConstructor) =
        Two.constant Y false := by
    simpa [implicationSubstitutionPair, prod.lift_map, Category.assoc] using ha
  simpa [implicationSubstitutionPair, prod.lift_map, prod.comp_lift_assoc,
    Category.assoc] using
    S.implication_absent_value (k ≫ p) (k ≫ a) (k ≫ b)
      (S.formulaPairGood_comp p a ga k) (S.formulaPairGood_comp p b gb k)
      (by simpa only [Category.assoc] using ha')

theorem quantifier_pair_good {X : D} (p : X ⟶ S.substitutionParameters)
    (y : X ⟶ V) (a : X ⟶ S.substitutionCarriers.2) (good : S.formulaPairGood p a) :
    S.formulaPairGood p (prod.lift p (prod.lift y a) ≫ S.quantifierSubstitutionPair) := by
  apply S.formulaPairGood_of_fixed
  intro Y k ha
  have ha' : S.formulaAbsenceTest (k ≫ p)
      (prod.lift (k ≫ y) (k ≫ a ≫ prod.fst) ≫ S.quantifierConstructor) =
        Two.constant Y false := by
    simpa [quantifierSubstitutionPair, quantifierOriginal, Category.assoc] using ha
  simpa [quantifierSubstitutionPair, quantifierOriginal, prod.comp_lift_assoc,
    Category.assoc] using S.quantifier_absent_value (k ≫ p) (k ≫ y) (k ≫ a)
      (S.formulaPairGood_comp p a good k) (by simpa only [Category.assoc] using ha')

end CategoricalEssentialIncompleteness.V46.CategoricalSyntax
