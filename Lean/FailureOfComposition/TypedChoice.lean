/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.TypedRecursionCategory
import PCats.DomSemilattice

/-!
# Choice for the typed program category

For a normalized program `q`, the inverse relation sends an output `y` to
any input `x` for which `q` sends `x` to `y`.  This relation need not be
functional.  A zero-valued semidecision program for it nevertheless feeds the
fair candidate-and-stage search, which selects one successful input whenever
one exists.  The resulting program is a partial section of `q`.

The search construction and its correctness are internal to arbitrary models
of PA.  Choosing the semidecision program is external and uses
`Classical.choose`; no effective dependence of that choice on `q` is asserted.
After source-target normalization, the selected program defines a typed
section.  Its two section equations hold in the uniform-provability quotient,
giving categorical choice, weak choice, and total range lifting.
-/

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoricalRiceShapiro.PartialRecursive
open Metamath.Feferman Arith.Feferman.Specialization

namespace FailureOfComposition.TypedChoice

open CodedObjectMembership ConcreteEvaluator ProofSearch ProgramGraph
open SigmaOneRealization SigmaOneSearch TypedProgramCategory TypedNearProduct
open TypedRanges TypedRecursionCategory UniformIndexQuotient
open PCategoryStruct CategoryTheory.RecursionCategory

noncomputable section

/-! ## Fair search in the inverse relation -/

/-- The inverse relation of the graph of `q`.  Its variables are an output of
`q` and a candidate preimage, in that order. -/
def inverseGraph (q : ℕ) : Graph :=
  .mkSigma “y x. !(eventualGraph q).val x y”

@[simp] theorem inverseGraph_eval
    {M : Type*} [ORingStructure M] (q : ℕ) (y x : M) :
    (inverseGraph q).val.Evalb ![y, x] ↔
      (eventualGraph q).val.Evalb ![x, y] := by
  simp [inverseGraph]

/-- A selected zero-valued semidecision program for the inverse relation.
The selection is external; no primitive-recursiveness claim is made. -/
def inverseSemidecisionCode (q : ℕ) : ProgramGraph.PCode :=
  Classical.choose
    (semidecision_exists (inverseGraph q).val (inverseGraph q).sigma_prop)

/-- Correctness of the selected inverse-relation semidecision program in
every PA model. -/
theorem inverseSemidecisionCode_spec (q : ℕ) :
    Semidecides (inverseGraph q).val (inverseSemidecisionCode q) :=
  Classical.choose_spec
    (semidecision_exists (inverseGraph q).val (inverseGraph q).sigma_prop)

/-- The program searched for a preimage.  Search is fair over encoded
candidate-and-computation-stage pairs. -/
def sectionSearchCode (q : ℕ) : ProgramGraph.PCode :=
  candidateSearch (reorderProgram (inverseSemidecisionCode q))

/-- The production index of the selected partial inverse program. -/
def sectionIndex (q : ℕ) : ℕ :=
  encode (sectionSearchCode q)

/-- Reordering converts a candidate/input pair for search into the vector
consumed by the inverse-relation semidecision program. -/
theorem computes_reordered_inverse
    {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (q : ℕ) (y x z : M) :
    Computes (reorderProgram (inverseSemidecisionCode q)) (pair x y) z ↔
      z = 0 ∧ (eventualGraph q).val.Evalb ![x, y] := by
  let : M↓[ℒₒᵣ] ⊧* 𝗜𝚺 1 :=
    models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝗣𝗔 from inferInstance)
  let : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 :=
    models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝗜𝚺 1 from inferInstance)
  rw [computes_reorder,
    inverseSemidecisionCode_spec q M ![y, x] z]
  simp only [inverseGraph_eval]

/-- Every value returned by the section program maps to its input under the original program. -/
theorem sectionIndex_sound
    {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (q : ℕ) (y x : M)
    (h : (eventualGraph (sectionIndex q)).val.Evalb ![y, x]) :
    (eventualGraph q).val.Evalb ![x, y] := by
  let : M↓[ℒₒᵣ] ⊧* 𝗜𝚺 1 :=
    models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝗣𝗔 from inferInstance)
  let : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 :=
    models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝗜𝚺 1 from inferInstance)
  have hs : Computes (sectionSearchCode q) y x := by
    simpa only [sectionIndex, Computes] using h
  have hr := candidateSearch_sound
    (reorderProgram (inverseSemidecisionCode q)) y x hs
  exact (computes_reordered_inverse q y x 0).mp hr |>.2

/-- Fair search is defined at `y` exactly when `y` has some preimage under
`q`.  This is an existential domain statement, not candidatewise equality of
the inverse relation and the selected program. -/
theorem sectionIndex_domain
    {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (q : ℕ) (y : M) :
    (∃ x : M, (eventualGraph (sectionIndex q)).val.Evalb ![y, x]) ↔
      ∃ x : M, (eventualGraph q).val.Evalb ![x, y] := by
  let : M↓[ℒₒᵣ] ⊧* 𝗜𝚺 1 :=
    models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝗣𝗔 from inferInstance)
  let : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 :=
    models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝗜𝚺 1 from inferInstance)
  change (∃ x : M, Computes (sectionSearchCode q) y x) ↔ _
  rw [sectionSearchCode, candidateSearch_domain]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, (computes_reordered_inverse q y x 0).mp hx |>.2⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, (computes_reordered_inverse q y x 0).mpr ⟨rfl, hx⟩⟩

/-! ## Internal selection assertions -/

/-- The internal assertion that a selected inverse computation is sound. -/
def selectionSoundnessSentence (q s : ℕ) : ArithmeticSentence :=
  “∀ y x, !(eventualGraph s).val y x → !(eventualGraph q).val x y”

/-- The internal assertion that the selected inverse and the original program
have matching existential domains in opposite directions. -/
def selectionDomainSentence (q s : ℕ) : ArithmeticSentence :=
  “∀ y, (∃ x, !(eventualGraph s).val y x) ↔
    ∃ x, !(eventualGraph q).val x y”

@[simp] theorem selectionSoundnessSentence_eval
    {M : Type*} [ORingStructure M] (q s : ℕ) :
    (selectionSoundnessSentence q s).Evalb (M := M) ![] ↔
      ∀ y x : M, (eventualGraph s).val.Evalb ![y, x] →
        (eventualGraph q).val.Evalb ![x, y] := by
  simp [selectionSoundnessSentence]

@[simp] theorem selectionDomainSentence_eval
    {M : Type*} [ORingStructure M] (q s : ℕ) :
    (selectionDomainSentence q s).Evalb (M := M) ![] ↔
      ∀ y : M,
        (∃ x : M, (eventualGraph s).val.Evalb ![y, x]) ↔
          ∃ x : M, (eventualGraph q).val.Evalb ![x, y] := by
  simp [selectionDomainSentence]

/-- PA proves the soundness of the selected partial inverse. -/
theorem pa_proves_sectionIndex_soundness (q : ℕ) :
    𝗣𝗔 ⊢ selectionSoundnessSentence q (sectionIndex q) := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff, selectionSoundnessSentence_eval]
  exact sectionIndex_sound q

/-- PA proves exact agreement of the two existential domains. -/
theorem pa_proves_sectionIndex_domain (q : ℕ) :
    𝗣𝗔 ⊢ selectionDomainSentence q (sectionIndex q) := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff, selectionDomainSentence_eval]
  exact sectionIndex_domain q

/-! ## Typed representatives and their section equations -/

/-- The selected section index of the actual normalized representative of a
raw typed program. -/
def typedSectionIndex (Q R : STObjectCode) (r : ℕ) : ℕ :=
  sectionIndex (normalizeIndex Q R r)

/-- Soundness of the typed selected section before its own normalization. -/
theorem typedSectionIndex_sound
    {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (Q R : STObjectCode) (r : ℕ) (y x : M)
    (h : (eventualGraph (typedSectionIndex Q R r)).val.Evalb ![y, x]) :
    (eventualGraph (normalizeIndex Q R r)).val.Evalb ![x, y] :=
  sectionIndex_sound (normalizeIndex Q R r) y x h

/-- The selected typed section is defined exactly on the range of the
normalized representative. -/
theorem typedSectionIndex_domain
    {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (Q R : STObjectCode) (r : ℕ) (y : M) :
    (∃ x : M,
      (eventualGraph (typedSectionIndex Q R r)).val.Evalb ![y, x]) ↔
      ∃ x : M,
        (eventualGraph (normalizeIndex Q R r)).val.Evalb ![x, y] :=
  sectionIndex_domain (normalizeIndex Q R r) y

/-- PA proves that the selected inverse program is supported from `R` to
`Q`. -/
theorem pa_proves_typedSectionIndex_support
    (Q R : STObjectCode) (r : ℕ) :
    𝗣𝗔 ⊢ supportSentence R Q (typedSectionIndex Q R r) := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff, supportSentence_eval]
  intro y x hs
  have hq := typedSectionIndex_sound Q R r y x hs
  obtain ⟨hQ, -, hR⟩ :=
    (eventualGraph_normalizeIndex_eval Q R r x y).mp hq
  exact ⟨hR, hQ⟩

/-- Normalizing the selected inverse from `R` to `Q` leaves its graph
PA-uniformly unchanged. -/
theorem typedSectionIndex_normalize_eq
    (Q R : STObjectCode) (r : ℕ) :
    EqIndex 𝗣𝗔
      (normalizeIndex R Q (typedSectionIndex Q R r))
      (typedSectionIndex Q R r) :=
  (proves_support_iff_eqIndex_normalize 𝗣𝗔 R Q
    (typedSectionIndex Q R r)).mp
      (pa_proves_typedSectionIndex_support Q R r)

/-- Exact graph equation after the selected section is normalized to its
typed source and target. -/
@[simp] theorem eventualGraph_normalize_typedSectionIndex_eval
    {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (Q R : STObjectCode) (r : ℕ) (y x : M) :
    (eventualGraph
      (normalizeIndex R Q (typedSectionIndex Q R r))).val.Evalb ![y, x] ↔
      (eventualGraph (typedSectionIndex Q R r)).val.Evalb ![y, x] := by
  rw [eventualGraph_normalizeIndex_eval]
  constructor
  · exact fun h => h.2.1
  · intro hs
    have hq := typedSectionIndex_sound Q R r y x hs
    obtain ⟨hQ, -, hR⟩ :=
      (eventualGraph_normalizeIndex_eval Q R r x y).mp hq
    exact ⟨hR, hs, hQ⟩

/-- Soundness of the normalized typed section. -/
theorem normalizedTypedSection_sound
    {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (Q R : STObjectCode) (r : ℕ) (y x : M)
    (h : (eventualGraph
      (normalizeIndex R Q (typedSectionIndex Q R r))).val.Evalb ![y, x]) :
    (eventualGraph (normalizeIndex Q R r)).val.Evalb ![x, y] :=
  typedSectionIndex_sound Q R r y x
    ((eventualGraph_normalize_typedSectionIndex_eval Q R r y x).mp h)

/-- The normalized selected section has exactly the range of the normalized
forward representative as its existential domain. -/
theorem normalizedTypedSection_domain
    {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (Q R : STObjectCode) (r : ℕ) (y : M) :
    (∃ x : M, (eventualGraph
      (normalizeIndex R Q (typedSectionIndex Q R r))).val.Evalb ![y, x]) ↔
      ∃ x : M,
        (eventualGraph (normalizeIndex Q R r)).val.Evalb ![x, y] := by
  constructor
  · rintro ⟨x, hx⟩
    exact (typedSectionIndex_domain Q R r y).mp
      ⟨x, (eventualGraph_normalize_typedSectionIndex_eval Q R r y x).mp hx⟩
  · intro h
    obtain ⟨x, hx⟩ := (typedSectionIndex_domain Q R r y).mpr h
    exact ⟨x,
      (eventualGraph_normalize_typedSectionIndex_eval Q R r y x).mpr hx⟩

/-- The selected typed section arrow associated with a raw representative. -/
def typedSectionArrow
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q R : STObjectCode) (r : ℕ) : object T R ⟶ object T Q :=
  arrowOfIndex T R Q (typedSectionIndex Q R r)

/-- Composing the selected section with the forward representative gives the
restriction of the section. -/
theorem eqIndex_section_comp
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q R : STObjectCode) (r : ℕ) :
    EqIndex T
      (compIndex (normalizeIndex Q R r)
        (normalizeIndex R Q (typedSectionIndex Q R r)))
      (domainIndex (normalizeIndex R Q (typedSectionIndex Q R r))) := by
  apply complete.{0} T
  intro M _ _
  have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 :=
    models_of_subtheory (U := T) inferInstance
  rw [models_iff, uniformSentence_eval]
  intro y z
  rw [eventualGraph_comp_eval, eventualGraph_domainIndex_eval]
  constructor
  · rintro ⟨x, hs, hqz⟩
    have hqy := normalizedTypedSection_sound Q R r y x hs
    have hyz := eventualGraph_output_unique
      (normalizeIndex Q R r) x y z hqy hqz
    exact ⟨hyz.symm, x, hs⟩
  · rintro ⟨hzy, x, hs⟩
    subst z
    exact ⟨x, hs, normalizedTypedSection_sound Q R r y x hs⟩

/-- Composing the forward representative, its selected section, and the
forward representative again returns the forward representative. -/
theorem eqIndex_comp_section_comp
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q R : STObjectCode) (r : ℕ) :
    EqIndex T
      (compIndex
        (compIndex (normalizeIndex Q R r)
          (normalizeIndex R Q (typedSectionIndex Q R r)))
        (normalizeIndex Q R r))
      (normalizeIndex Q R r) := by
  apply complete.{0} T
  intro M _ _
  have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 :=
    models_of_subtheory (U := T) inferInstance
  rw [models_iff, uniformSentence_eval]
  intro x y
  constructor
  · intro h
    obtain ⟨u, hxu, hinner⟩ :=
      (eventualGraph_comp_eval _ _ x y).mp h
    obtain ⟨z, huz, hzy⟩ :=
      (eventualGraph_comp_eval _ _ u y).mp hinner
    have hzu := normalizedTypedSection_sound Q R r u z huz
    have huy := eventualGraph_output_unique
      (normalizeIndex Q R r) z u y hzu hzy
    simpa only [huy] using hxu
  · intro hxy
    obtain ⟨z, hyz⟩ :=
      (normalizedTypedSection_domain Q R r y).mpr ⟨x, hxy⟩
    apply (eventualGraph_comp_eval _ _ x y).mpr
    refine ⟨y, hxy, ?_⟩
    exact (eventualGraph_comp_eval _ _ y y).mpr
      ⟨z, hyz, normalizedTypedSection_sound Q R r y z hyz⟩

/-- The first categorical section equation for the selected typed arrow. -/
theorem typedSectionArrow_comp_eq_rst
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q R : STObjectCode) (r : ℕ) :
    typedSectionArrow T Q R r ≫ arrowOfIndex T Q R r =
      rst (typedSectionArrow T Q R r) := by
  apply CodedHom.ext
  rw [comp_val,
    ← domainClass_eq_rst_val T R Q (typedSectionArrow T Q R r),
    typedSectionArrow, arrowOfIndex_val, arrowOfIndex_val]
  rw [mul_classOf, domainClass_classOf, classOf_eq_classOf_iff]
  exact eqIndex_section_comp T Q R r

/-- The second categorical section equation for the selected typed arrow. -/
theorem typedSectionArrow_comp_self
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q R : STObjectCode) (r : ℕ) :
    arrowOfIndex T Q R r ≫ typedSectionArrow T Q R r ≫
        arrowOfIndex T Q R r =
      arrowOfIndex T Q R r := by
  apply CodedHom.ext
  rw [comp_val, comp_val, typedSectionArrow, arrowOfIndex_val,
    arrowOfIndex_val]
  rw [mul_classOf, mul_classOf, classOf_eq_classOf_iff]
  exact eqIndex_comp_section_comp T Q R r

/-- Representative-level partial-section theorem. -/
theorem typedSectionArrow_isSection
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q R : STObjectCode) (r : ℕ) :
    IsSection (arrowOfIndex T Q R r) (typedSectionArrow T Q R r) where
  comp_eq_rst := typedSectionArrow_comp_eq_rst T Q R r
  comp_self := typedSectionArrow_comp_self T Q R r

/-! ## Choice, ranges, and total range lifting -/

/-- Every arrow in the typed program category has a partial section. -/
theorem exists_isSection
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    {Q R : CodedProgramCategory T} (f : Q ⟶ R) :
    ∃ σ : R ⟶ Q, IsSection f σ := by
  obtain ⟨r, hr⟩ := exists_arrowOfIndex T (objectCode Q) (objectCode R) f
  subst f
  exact ⟨typedSectionArrow T (objectCode Q) (objectCode R) r,
    typedSectionArrow_isSection T (objectCode Q) (objectCode R) r⟩

/-- The maintained typed program category satisfies categorical choice. -/
instance codedProgramCategoryHasChoice
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    HasChoice (CodedProgramCategory T) where
  exists_isSection := exists_isSection T

/-- The restriction of the representative-level selected section is the
existing categorical range, not a second range construction. -/
theorem typedSectionArrow_rst_eq_ran
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q R : STObjectCode) (r : ℕ) :
    rst (typedSectionArrow T Q R r) =
      HasRanges.ran (arrowOfIndex T Q R r) :=
  (typedSectionArrow_isSection T Q R r).rst_eq_ran

/-- Every typed arrow admits total lifting of total arrows through its
existing categorical range. -/
theorem codedProgramCategory_hasTotalRangeLifting
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    {Q R : CodedProgramCategory T} (f : Q ⟶ R) :
    HasTotalRangeLifting f :=
  hasTotalRangeLifting_of_hasChoice f

/-- Categorical choice implies weak choice for the typed program category. -/
instance codedProgramCategoryHasWeakChoice
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    HasWeakChoice (CodedProgramCategory T) :=
  hasWeakChoice_of_hasChoice

/-! ## Focused applications -/

/-- The identity arrow is a section of itself. -/
theorem identity_isSection
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (Q : STObjectCode) :
    IsSection (𝟙 (object T Q)) (𝟙 (object T Q)) where
  comp_eq_rst := by
    rw [Category.id_comp, PCategory.rst_id]
  comp_self := by simp

/-- The zero arrow in the opposite direction is a section of a categorical
zero arrow. -/
theorem zero_isSection
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (Q R : STObjectCode) :
    IsSection (0 : object T Q ⟶ object T R)
      (0 : object T R ⟶ object T Q) where
  comp_eq_rst := by
    rw [Limits.zero_comp, CategoryTheory.DomSemilattice.rst_zero]
  comp_self := by simp

/-- The existing range of a categorical zero arrow is zero, obtained from
the section/range comparison. -/
@[simp] theorem ran_zero
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (Q R : STObjectCode) :
    HasRanges.ran (0 : object T Q ⟶ object T R) = 0 := by
  rw [← (zero_isSection T Q R).rst_eq_ran,
    CategoryTheory.DomSemilattice.rst_zero]

/-- The total constant-zero endomorphism of `omega`.  This is not the
categorical zero, which is represented by the nowhere-defined program. -/
def omegaConstantZeroArrow
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    omegaObject T ⟶ omegaObject T :=
  arrowOfIndex T .omega .omega (encode (Nat.Partrec.Code.zero))

/-- The normalized total constant-zero program still maps every input to
zero in each PA model. -/
@[simp] theorem eventualGraph_normalize_constantZero_eval
    {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (x y : M) :
    (eventualGraph
      (normalizeIndex .omega .omega
        (encode (Nat.Partrec.Code.zero)))).val.Evalb ![x, y] ↔
      y = 0 := by
  rw [eventualGraph_normalizeIndex_eval]
  simp only [memberFormula_omega_eval, true_and, and_true]
  exact computes_zero x y

/-- At output zero, the inverse relation of the constant-zero endomorphism
contains two distinct preimages in every PA model. -/
theorem inverseGraph_constantZero_has_two_preimages
    {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] :
    (inverseGraph
      (normalizeIndex .omega .omega
        (encode (Nat.Partrec.Code.zero)))).val.Evalb ![(0 : M), 0] ∧
    (inverseGraph
      (normalizeIndex .omega .omega
        (encode (Nat.Partrec.Code.zero)))).val.Evalb ![(0 : M), 1] ∧
    (0 : M) ≠ 1 := by
  constructor
  · rw [inverseGraph_eval, eventualGraph_normalize_constantZero_eval]
  · constructor
    · rw [inverseGraph_eval, eventualGraph_normalize_constantZero_eval]
    · exact zero_ne_one

/-- The general search construction supplies a partial section of the total
constant-zero endomorphism without specifying which preimage it selects. -/
def omegaConstantZeroSection
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    omegaObject T ⟶ omegaObject T :=
  typedSectionArrow T .omega .omega (encode (Nat.Partrec.Code.zero))

theorem omegaConstantZeroSection_isSection
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    IsSection (omegaConstantZeroArrow T) (omegaConstantZeroSection T) :=
  typedSectionArrow_isSection T .omega .omega
    (encode (Nat.Partrec.Code.zero))

theorem omegaConstantZeroSection_rst_eq_ran
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    rst (omegaConstantZeroSection T) =
      HasRanges.ran (omegaConstantZeroArrow T) :=
  (omegaConstantZeroSection_isSection T).rst_eq_ran

end

end FailureOfComposition.TypedChoice
