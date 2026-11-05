import CategoricalEssentialIncompleteness.V46SyntacticDerivationTuples

/-! Positive rule-input guards and their actual root-conclusion graph. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open FailureOfComposition.ProofSearch FailureOfComposition.CodedObjectMembership
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.SyntacticDerivation
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

/-- The ordered premise graph is obtained from the actual categorical
map and the constructed encoder of its chosen finite-power codomain. -/
def encodedPremises {F : PredicateCategory T} {N : ℕ}
    (R : RulePresentation F N) (i : Fin (N + 1)) :
    GraphMorphism T (R.instances i) (tupleCarrier F i.val) :=
  (chosenGraph T (R.premises i)).composition (finitePowerEncoder T F i.val)

def encodedConclusion {F : PredicateCategory T} {N : ℕ}
    (R : RulePresentation F N) (i : Fin (N + 1)) : GraphMorphism T (R.instances i) F :=
  chosenGraph T (R.conclusion i)

namespace RuleInput
variable {T} {A B F : Carrier}
variable (p : GraphMorphism T A F) (q : GraphMorphism T B F)

/-- A literal input is a pair of a rule label and its ordered children.
A common tuple output positively certifies the premise match. -/
def carrier : Carrier := .mkSigma “u. ∃ r d z,
  !pairDef.val u r d ∧ !p.graph.val r z ∧ !q.graph.val d z”

def labelGraph : Graph := let C := carrier p q
  .mkSigma “u r. !C.val u ∧ !pi₁Def.val r u”

def childrenGraph : Graph := let C := carrier p q
  .mkSigma “u d. !C.val u ∧ !pi₂Def.val d u”

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

omit [𝗣𝗔 ⪯ T] [M↓[ℒₒᵣ] ⊧* T] in
@[simp] theorem carrier_eval (u : M) :
    (carrier p q).val.Evalb ![u] ↔ ∃ r d z : M,
      u = Arithmetic.pair r d ∧ p.graph.val.Evalb ![r, z] ∧ q.graph.val.Evalb ![d, z] := by
  simp [carrier]

omit [𝗣𝗔 ⪯ T] [M↓[ℒₒᵣ] ⊧* T] in
@[simp] theorem carrier_pair (r d : M) :
    (carrier p q).val.Evalb ![Arithmetic.pair r d] ↔
      ∃ z : M, p.graph.val.Evalb ![r, z] ∧ q.graph.val.Evalb ![d, z] := by
  rw [carrier_eval]
  constructor
  · rintro ⟨r', d', z, he, hp, hq⟩
    have hr : r = r' := by simpa only [pi₁_pair] using congrArg pi₁ he
    have hd : d = d' := by simpa only [pi₂_pair] using congrArg pi₂ he
    simpa only [hr, hd] using Exists.intro z (And.intro hp hq)
  · rintro ⟨z, hp, hq⟩
    exact ⟨r, d, z, rfl, hp, hq⟩

omit [𝗣𝗔 ⪯ T] [M↓[ℒₒᵣ] ⊧* T] in
@[simp] theorem labelGraph_eval (u r : M) :
    (labelGraph p q).val.Evalb ![u, r] ↔
      (carrier p q).val.Evalb ![u] ∧ r = π₁ u := by
  have h (x y : M) : pi₁Def.val.Evalb ![x, y] ↔ x = π₁ y := pi₁_defined.iff
  simp [labelGraph, h]

omit [𝗣𝗔 ⪯ T] [M↓[ℒₒᵣ] ⊧* T] in
@[simp] theorem childrenGraph_eval (u d : M) :
    (childrenGraph p q).val.Evalb ![u, d] ↔
      (carrier p q).val.Evalb ![u] ∧ d = π₂ u := by
  have h (x y : M) : pi₂Def.val.Evalb ![x, y] ↔ x = π₂ y := pi₂_defined.iff
  simp [childrenGraph, h]

omit [𝗣𝗔 ⪯ T] in
theorem carrier_components (u : M) (hu : (carrier p q).val.Evalb ![u]) :
    A.val.Evalb ![π₁ u] ∧ B.val.Evalb ![π₂ u] ∧
      ∃ z : M, p.graph.val.Evalb ![π₁ u, z] ∧ q.graph.val.Evalb ![π₂ u, z] := by
  obtain ⟨r, d, z, rfl, hp, hq⟩ := (carrier_eval p q u).mp hu
  simpa only [pi₁_pair, pi₂_pair] using
    And.intro (p.support_model M r z hp).1
      (And.intro (q.support_model M d z hq).1 ⟨z, hp, hq⟩)

omit [𝗣𝗔 ⪯ T] in
/-- On the actual positive matching domain, both premise computations
have the same value, with no comparison of Sigma-one nonmembership. -/
theorem match_iff (u z : M) (hu : (carrier p q).val.Evalb ![u]) :
    p.graph.val.Evalb ![π₁ u, z] ↔ q.graph.val.Evalb ![π₂ u, z] := by
  obtain ⟨hA, hB, w, hp, hq⟩ := carrier_components p q u hu
  constructor
  · intro hz
    have he := (p.total_model M (π₁ u) hA).unique hz hp
    simpa only [he] using hq
  · intro hz
    have he := (q.total_model M (π₂ u) hB).unique hz hq
    simpa only [he] using hp

end Models

def label : GraphMorphism T (carrier p q) A where
  graph := labelGraph p q
  support := by
    apply complete.{0} T
    intro M _ hM
    let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) hM
    rw [models_iff, supportSentence_eval]
    intro u r h
    obtain ⟨hu, rfl⟩ := (labelGraph_eval p q u r).mp h
    exact ⟨hu, (carrier_components p q u hu).1⟩
  total := by
    apply complete.{0} T
    intro M _ hM
    let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) hM
    rw [models_iff, totalSentence_eval]
    intro u hu
    exact ⟨π₁ u, (labelGraph_eval p q u _).mpr ⟨hu, rfl⟩,
      fun r hr => ((labelGraph_eval p q u r).mp hr).2⟩

def children : GraphMorphism T (carrier p q) B where
  graph := childrenGraph p q
  support := by
    apply complete.{0} T
    intro M _ hM
    let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) hM
    rw [models_iff, supportSentence_eval]
    intro u d h
    obtain ⟨hu, rfl⟩ := (childrenGraph_eval p q u d).mp h
    exact ⟨hu, (carrier_components p q u hu).2.1⟩
  total := by
    apply complete.{0} T
    intro M _ hM
    let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) hM
    rw [models_iff, totalSentence_eval]
    intro u hu
    exact ⟨π₂ u, (childrenGraph_eval p q u _).mpr ⟨hu, rfl⟩,
      fun d hd => ((childrenGraph_eval p q u d).mp hd).2⟩

/-- The two typed projections give the actual commutative matching square. -/
theorem square :
    representedArrow T (label p q) ≫ representedArrow T p =
      representedArrow T (children p q) ≫ representedArrow T q := by
  apply hom_ext T
  intro M _ hM u z
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) hM
  simp only [relation_comp, relation_class]
  change (∃ r : M, (labelGraph p q).val.Evalb ![u, r] ∧ p.graph.val.Evalb ![r, z]) ↔
    ∃ d : M, (childrenGraph p q).val.Evalb ![u, d] ∧ q.graph.val.Evalb ![d, z]
  constructor
  · rintro ⟨r, hr, hz⟩
    obtain ⟨hu, rfl⟩ := (labelGraph_eval p q u r).mp hr
    exact ⟨π₂ u, (childrenGraph_eval p q u _).mpr ⟨hu, rfl⟩,
      (match_iff p q u z hu).mp hz⟩
  · rintro ⟨d, hd, hz⟩
    obtain ⟨hu, rfl⟩ := (childrenGraph_eval p q u d).mp hd
    exact ⟨π₁ u, (labelGraph_eval p q u _).mpr ⟨hu, rfl⟩,
      (match_iff p q u z hu).mpr hz⟩

/-- A nullary input has its literal empty tuple; availability depends
only on the rule label, as in the nullary component of H_R. -/
theorem nullary_carrier {Q F : Carrier} (p : GraphMorphism T A (tupleCarrier F 0))
    (q : GraphMorphism T Q F)
    (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (r d : M) :
    (carrier p (tupleMorphism q 0)).val.Evalb ![Arithmetic.pair r d] ↔
      A.val.Evalb ![r] ∧ d = 0 := by
  rw [carrier_pair]
  constructor
  · rintro ⟨z, hp, hq⟩
    have hq' : d = 0 ∧ z = 0 := (tupleGraph_zero q.graph d z).mp hq
    exact ⟨(p.support_model M r z hp).1, hq'.1⟩
  · rintro ⟨hr, rfl⟩
    obtain ⟨z, hz, _⟩ := p.total_model M r hr
    have hz' : z = 0 := (tupleCarrier_zero F z).mp (p.support_model M r z hz).2
    refine ⟨z, hz, ?_⟩
    exact (tupleGraph_zero q.graph 0 z).mpr ⟨rfl, hz'⟩

end RuleInput

variable {T} {F Q : PredicateCategory T} {N : ℕ}
variable (R : RulePresentation F N) (q : GraphMorphism T Q F)

/-- Literal source for the n-th inference summand. Each child's own
conclusion is computed by q; the parent conclusion is not its parameter. -/
def ruleInputCarrier (i : Fin (N + 1)) : Carrier :=
  RuleInput.carrier (encodedPremises T R i) (tupleMorphism q i.val)

def ruleInputLabel (i : Fin (N + 1)) :
    GraphMorphism T (ruleInputCarrier R q i) (R.instances i) :=
  RuleInput.label (encodedPremises T R i) (tupleMorphism q i.val)

def ruleInputChildren (i : Fin (N + 1)) :
    GraphMorphism T (ruleInputCarrier R q i) (tupleCarrier Q i.val) :=
  RuleInput.children (encodedPremises T R i) (tupleMorphism q i.val)

/-- The actual conclusion is q_n(r), independently of the individual
child conclusion indices used to certify the premise match. -/
def ruleInputConclusion (i : Fin (N + 1)) :
    GraphMorphism T (ruleInputCarrier R q i) F :=
  (ruleInputLabel R q i).composition (encodedConclusion T R i)

theorem ruleInput_square (i : Fin (N + 1)) :
    representedArrow T (ruleInputLabel R q i) ≫ representedArrow T (encodedPremises T R i) =
      representedArrow T (ruleInputChildren R q i) ≫ representedArrow T (tupleMorphism q i.val) :=
  RuleInput.square (encodedPremises T R i) (tupleMorphism q i.val)

end CategoricalEssentialIncompleteness.V46.SyntacticDerivation
