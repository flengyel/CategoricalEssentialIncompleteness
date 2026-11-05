import CategoricalEssentialIncompleteness.V46FiniteSigmaOne
import CategoricalEssentialIncompleteness.V46SyntacticSyntaxWords

/-! Positive finite evaluation records, including nonstandard model lengths. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment

namespace CategoricalEssentialIncompleteness.V46.SyntacticDerivation
namespace Records
abbrev Transition := 𝚺₁.Semisentence 3
abbrev Carrier := 𝚺₁.Semisentence 1

/-- An edge stores its input state, the next literal word record, and
its output state. No witness for transition membership occurs in this code. -/
def edgeCarrier (g : Transition) : Carrier := .mkSigma
  “e. ∃ s b r t, !pairDef.val e s b ∧ !pairDef.val b r t ∧ !g.val s r t”

/-- Finite collection supplies all transition witnesses simultaneously.
Only numerical vector reads and pair consistency checks remain bounded. -/
def run (g : Transition) : 𝚺₁.Semisentence 3 :=
  let C := FiniteSigmaOne.finiteMembership (edgeCarrier g)
  .mkSigma “word initial final. ∃ states edges l,
    !lenDef.val l word ∧ !lenDef.val (l + 1) states ∧ !lenDef.val l edges ∧
    !nthDef.val initial states 0 ∧ !nthDef.val final states l ∧ !C.val edges ∧
    ∀ i < l, ∃ s < states, ∃ r < word, ∃ t < states, ∃ e < edges, ∃ b < e + 1,
      !nthDef.val s states i ∧ !nthDef.val r word i ∧ !nthDef.val t states (i + 1) ∧
      !nthDef.val e edges i ∧ !pairDef.val e s b ∧ !pairDef.val b r t”

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
variable (g : Transition)

@[simp] theorem edgeCarrier_eval (e : M) :
    (edgeCarrier g).val.Evalb ![e] ↔
      g.val.Evalb ![π₁ e, π₁ (π₂ e), π₂ (π₂ e)] := by
  have hraw : (edgeCarrier g).val.Evalb ![e] ↔ ∃ s b r t : M,
      e = Arithmetic.pair s b ∧ b = Arithmetic.pair r t ∧ g.val.Evalb ![s, r, t] := by
    simp [edgeCarrier]
  rw [hraw]
  constructor
  · rintro ⟨s, b, r, t, rfl, rfl, h⟩
    simpa only [pi₁_pair, pi₂_pair] using h
  · intro h
    exact ⟨π₁ e, π₂ e, π₁ (π₂ e), π₂ (π₂ e), (pair_unpair e).symm,
      (pair_unpair (π₂ e)).symm, h⟩

theorem run_raw_eval (word initial final : M) :
    (run g).val.Evalb ![word, initial, final] ↔ ∃ states edges l : M,
      l = len word ∧ l + 1 = len states ∧ l = len edges ∧
      initial = nth states 0 ∧ final = nth states l ∧
      (FiniteSigmaOne.finiteMembership (edgeCarrier g)).val.Evalb ![edges] ∧
      ∀ i < l, ∃ s < states, ∃ r < word, ∃ t < states, ∃ e < edges, ∃ b < e + 1,
        s = nth states i ∧ r = nth word i ∧ t = nth states (i + 1) ∧
        e = nth edges i ∧ e = Arithmetic.pair s b ∧ b = Arithmetic.pair r t := by
  simp [run]

/-- The Sigma-one formula describes exactly an actual state at every
position of the word, even when the word has nonstandard model length. -/
theorem run_iff_trace (word initial final : M) :
    (run g).val.Evalb ![word, initial, final] ↔ ∃ states : M,
      len states = len word + 1 ∧ nth states 0 = initial ∧ nth states (len word) = final ∧
      ∀ i < len word, g.val.Evalb ![nth states i, nth word i, nth states (i + 1)] := by
  rw [run_raw_eval]
  constructor
  · rintro ⟨states, edges, l, rfl, hs, he, h₀, hf, hm, hr⟩
    have hm' := (FiniteSigmaOne.allEntriesCondition_eval (edgeCarrier g) edges).mp
      ((FiniteSigmaOne.finite_membership_model (edgeCarrier g) edges).mpr hm)
    refine ⟨states, hs.symm, h₀.symm, hf.symm, ?_⟩
    intro i hi
    obtain ⟨s, _, r, _, t, _, e, _, b, _, rfl, rfl, rfl, hee, hes, hbr⟩ := hr i hi
    have hg := (edgeCarrier_eval g e).mp (by
      rw [hee]
      exact hm' i (by simpa only [← he] using hi))
    simpa only [hes, hbr, pi₁_pair, pi₂_pair] using hg
  · rintro ⟨states, hs, h₀, hf, hg⟩
    have hR : 𝚺₁-Relation (fun i e : M =>
        e = Arithmetic.pair (nth states i)
          (Arithmetic.pair (nth word i) (nth states (i + 1)))) := by
      definability
    obtain ⟨edges, he, hee⟩ := sigmaOne_skolem_vec hR
      (fun i (_ : i < len word) => ⟨Arithmetic.pair (nth states i)
        (Arithmetic.pair (nth word i) (nth states (i + 1))), rfl⟩)
    have hm : (FiniteSigmaOne.finiteMembership (edgeCarrier g)).val.Evalb ![edges] := by
      apply (FiniteSigmaOne.finite_membership_model (edgeCarrier g) edges).mp
      apply (FiniteSigmaOne.allEntriesCondition_eval (edgeCarrier g) edges).mpr
      intro i hi
      have hi' : i < len word := by simpa only [he] using hi
      rw [edgeCarrier_eval, hee i hi']
      simpa only [pi₁_pair, pi₂_pair] using hg i hi'
    refine ⟨states, edges, len word, rfl, hs.symm, he.symm, h₀.symm, hf.symm, hm, ?_⟩
    intro i hi
    have his : i < len states := lt_trans hi (by rw [hs]; simp)
    have hit : i + 1 < len states := by simpa only [hs, add_lt_add_iff_right] using hi
    refine ⟨nth states i, nth_lt_self his, nth word i, nth_lt_self hi,
      nth states (i + 1), nth_lt_self hit, nth edges i, nth_lt_self (by simpa only [he] using hi),
      Arithmetic.pair (nth word i) (nth states (i + 1)), ?_, rfl, rfl, rfl, rfl, hee i hi, rfl⟩
    rw [hee i hi]
    exact Arithmetic.lt_succ_iff_le.mpr (le_pair_right _ _)

@[simp] theorem run_nil (initial final : M) :
    (run g).val.Evalb ![0, initial, final] ↔ final = initial := by
  rw [run_iff_trace]
  constructor
  · rintro ⟨states, _, h₀, hf, _⟩
    have hf' : nth states 0 = final := by simpa only [len_nil] using hf
    exact hf'.symm.trans h₀
  · intro h
    subst final
    refine ⟨adjoin initial 0, by simp, by simp, by simp, ?_⟩
    simp

/-- PA induction compares the two actual vectors at each numerical
position, including positions in nonstandard models. -/
theorem run_functional
    (hfun : ∀ s r y z : M, g.val.Evalb ![s, r, y] → g.val.Evalb ![s, r, z] → y = z)
    (word initial y z : M)
    (hy : (run g).val.Evalb ![word, initial, y])
    (hz : (run g).val.Evalb ![word, initial, z]) : y = z := by
  obtain ⟨s, _, hs₀, hsy, hs⟩ := (run_iff_trace g word initial y).mp hy
  obtain ⟨t, _, ht₀, htz, ht⟩ := (run_iff_trace g word initial z).mp hz
  have hP : 𝚷₁-Predicate (fun i : M => i ≤ len word → nth s i = nth t i) := by
    let l := len word
    let N : 𝚺₁.Semiformula M 3 := nthDef.rew Rew.emb
    refine ⟨.mkPi “i. i ≤ &l → ∀ a b,
      !N.val a &s i → !N.val b &t i → a = b”, ?_⟩
    intro v
    simp [N, l]
  have hh : ∀ i ≤ len word, nth s i = nth t i := by
    intro i
    induction i using ISigma1.pi1_succ_induction
    · exact hP
    case zero => intro _; exact hs₀.trans ht₀.symm
    case succ i ih =>
      intro hi
      have hi' : i < len word := by simpa only [Arithmetic.succ_le_iff_lt] using hi
      have hi₀ : i ≤ len word := le_of_lt hi'
      apply hfun (nth s i) (nth word i) _ _ (hs i hi')
      simpa only [ih hi₀] using ht i hi'
  exact hsy.symm.trans ((hh (len word) le_rfl).trans htz)

end Models

/-- PA itself proves that locally functional transitions give a
functional finite-record run. No total transition extension is required. -/
def functionalitySentence (g : Transition) : ArithmeticSentence :=
  let E := run g
  “(∀ s r y z, !g.val s r y → !g.val s r z → y = z) →
    ∀ word initial y z, !E.val word initial y → !E.val word initial z → y = z”

theorem run_functionality_PA (g : Transition) : 𝗣𝗔 ⊢ functionalitySentence g := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff]
  have h : (∀ s r y z : M, g.val.Evalb ![s, r, y] → g.val.Evalb ![s, r, z] → y = z) →
      ∀ word initial y z : M,
        (run g).val.Evalb ![word, initial, y] → (run g).val.Evalb ![word, initial, z] → y = z :=
    fun hg word initial y z hy hz => run_functional g hg word initial y z hy hz
  simpa [functionalitySentence] using h

end Records
end CategoricalEssentialIncompleteness.V46.SyntacticDerivation
