import CategoricalEssentialIncompleteness.V46ConcreteNamedSubstitutionTraversal
import CategoricalEssentialIncompleteness.V46SyntacticSyntaxRefillLaws

/-! Internal PA composition and stack-frame laws for the actual numerical
traversal. The root computations are the given globally total numeric functions. -/
noncomputable section
local instance primitiveNamedTraversalLawsDecidableEqNat : DecidableEq ℕ := Classical.decEq ℕ
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedSubstitution.Traversal
open SyntacticSyntax SyntacticSyntax.Coding
section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
variable (a b : RawPolynomial) (F G : 𝚺₁.Semisentence 3)
  (f g : M → M → M) [𝚺₁-Function₂ f via F] [𝚺₁-Function₂ g via G]
  (param : M)
local instance : DecidableEq M := Classical.decEq M

/-- A successful root step consumes only its polynomial's stack prefix. -/
theorem step_frame (record stack out tail : M)
    (h : step a b f g param record (stack + 1) = out + 1) :
    step a b f g param record (Words.append stack tail + 1) = Words.append out tail + 1 := by
  by_cases hk₀ : π₂ record = 0
  · rcases nil_or_adjoin (refill a (π₁ record) stack) with hl | ⟨u,rest,hl⟩
    · simp [step,hk₀,hl] at h
    · have hout : out = adjoin ⟪f param u,0⟫ rest := by
        symm
        simpa [step,hk₀,hl] using h
      rw [hout]
      simp [step,hk₀,refill_frame a (π₁ record) stack u rest tail hl]
  · by_cases hk₁ : π₂ record = 1
    · rcases nil_or_adjoin (refill b (π₁ record) stack) with hr | ⟨u,rest,hr⟩
      · simp [step,hk₁,hr] at h
      · have hout : out = adjoin ⟪g param u,1⟫ rest := by
          symm
          simpa [step,hk₁,hr] using h
        rw [hout]
        simp [step,hk₁,refill_frame b (π₁ record) stack u rest tail hr]
    · simp [step,hk₀,hk₁] at h

theorem prefix_frame (word n stack out tail : M)
    (h : runPrefix a b F G f g param word n (stack + 1) = out + 1) :
    runPrefix a b F G f g param word n (Words.append stack tail + 1) = Words.append out tail + 1 := by
  induction n using ISigma1.pi1_succ_induction generalizing stack out tail
  · definability
  case zero =>
    have ho : stack = out := by simpa using h
    simp [ho]
  case succ n ih =>
    rcases zero_or_succ (runPrefix a b F G f g param word n (stack + 1)) with hz | ⟨prev,hp⟩
    · simp [prefix_succ,hz] at h
    · rw [prefix_succ,hp] at h
      rw [prefix_succ,ih stack prev tail hp]
      exact step_frame a b f g param (nth word n) prev out tail h

theorem run_frame (word stack out tail : M)
    (h : run a b F G f g param word (stack + 1) = out + 1) :
    run a b F G f g param word (Words.append stack tail + 1) = Words.append out tail + 1 :=
  prefix_frame a b F G f g param word (len word) stack out tail h

theorem prefix_congr (word other n initial : M) (h : ∀ i < n,nth word i = nth other i) :
    runPrefix a b F G f g param word n initial = runPrefix a b F G f g param other n initial := by
  induction n using ISigma1.pi1_succ_induction generalizing word other initial
  · definability
  case zero => simp
  case succ n ih =>
    have hp : ∀ i < n,nth word i = nth other i := fun i hi => h i (lt_trans hi (by simp))
    rw [prefix_succ,prefix_succ,ih word other initial hp,h n (by simp)]

theorem prefix_append (word suffix k initial : M) :
    runPrefix a b F G f g param (Words.append word suffix) (len word + k) initial =
      runPrefix a b F G f g param suffix k (run a b F G f g param word initial) := by
  induction k using ISigma1.pi1_succ_induction
  · definability
  case zero =>
    simpa [run] using prefix_congr a b F G f g param (Words.append word suffix) word
      (len word) initial (fun i hi => Words.nth_append_left word suffix i hi)
  case succ k ih =>
    have he : len word + (k + 1) = (len word + k) + 1 := by simp [add_assoc]
    rw [he,prefix_succ,prefix_succ,Words.nth_append_right,ih]

theorem run_append (word suffix initial : M) :
    run a b F G f g param (Words.append word suffix) initial =
      run a b F G f g param suffix (run a b F G f g param word initial) := by
  unfold run
  rw [Words.len_append,prefix_append]
  rfl

@[simp] theorem run_snoc (word record initial : M) :
    run a b F G f g param (concat word record) initial =
      step a b f g param record (run a b F G f g param word initial) := by
  rw [← Words.append_singleton,run_append]
  have hlen : len (adjoin record (0 : M)) = 0 + 1 := by simp
  change runPrefix a b F G f g param (adjoin record 0) (len (adjoin record 0))
    (run a b F G f g param word initial) = _
  rw [hlen,prefix_succ]
  simp

end Models
end CategoricalEssentialIncompleteness.V46.ConcreteNamedSubstitution.Traversal
