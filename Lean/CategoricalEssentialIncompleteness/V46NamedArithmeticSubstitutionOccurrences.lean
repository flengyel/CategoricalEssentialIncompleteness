import CategoricalEssentialIncompleteness.V46NamedArithmeticModelSubstitution
import CategoricalEssentialIncompleteness.V46NamedArithmeticQuantifierOccurrences

/-! The free variables of substitution into a fixed finite named source
formula, in any PA model and for an arbitrary internal closed replacement.
The induction is on that source formula, never on external finiteness of
the model's internal replacement word. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Coding
namespace CategoricalEssentialIncompleteness.V46.NamedArithmeticSubstitutionOccurrences
open ConcreteNamedSubstitution NamedPostfixEncoding NamedArithmeticModelCoding
open NamedArithmeticModelSubstitution NamedArithmeticModelOccurrences NamedArithmeticQuantifierOccurrences
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance namedArithmeticSubstitutionOccurrencesDecidableEq : DecidableEq M := Classical.decEq M
variable (σ π : ℕ → Carrier) (d : ℕ)
local notation "Tm" => Postfix.carrier false (termPolynomial σ d) (formulaPolynomial π d)
local notation "FV" => ConcreteNamedSubstitution.freeVariables variableCarrier σ π d

private theorem member_append_one (name s t : M) :
    member name (Words.append s t) = 1 ↔ member name s = 1 ∨ member name t = 1 := by
  rw [member_append]
  by_cases h : member name s = 1 <;> simp [h]

 theorem termOutput_member_iff (x replacement : M)
    (hrep : (Tm).val.Evalb ![replacement]) (hclosed : FV replacement = 0)
    (s : NamedFiniteSyntax.Term (Symbols σ) d) (name : M) :
    member name (FV (termOutput (M := M) (σ := σ) (d := d) x replacement s)) = 1 ↔
      name ≠ x ∧ member name (FV (termWord (M := M) (σ := σ) (d := d) s)) = 1 := by
  induction s with
  | var y =>
    have hv : FV (termWord (M := M) (σ := σ) (d := d) (NamedFiniteSyntax.Term.var y : NamedFiniteSyntax.Term (Symbols σ) d)) = adjoin (y : M) 0 :=
      freeVariables_variable (M := M) variableCarrier σ π d (y : M) (by simp [variableCarrier])
    by_cases hy : (y : M) = x
    · simp only [termOutput,hy,ite_true,hclosed,member_nil,hv,member_adjoin]
      by_cases hz : (y : M) = name <;> simp_all
    · simp only [termOutput,hy,ite_false,hv,member_adjoin,member_nil]
      by_cases hz : (y : M) = name <;> simp_all
  | app k s children ih =>
    rw [termOutput,termWord,
      function_occurrences (M := M) σ π d k s (fun i => termOutput (M := M) (σ := σ) (d := d) x replacement (children i))
        (fun i => termOutput_member (M := M) (σ := σ) (d := d) π x replacement hrep (children i)),
      function_occurrences (M := M) σ π d k s (fun i => termWord (M := M) (σ := σ) (d := d) (children i))
        (fun i => termWord_member (M := M) (σ := σ) (d := d) π (children i)),
      member_gatherTuple (M := M),member_gatherTuple (M := M)]
    constructor
    · rintro ⟨i,hi⟩
      exact ⟨((ih i).mp hi).1,⟨i,((ih i).mp hi).2⟩⟩
    · rintro ⟨hne,i,hi⟩
      exact ⟨i,(ih i).mpr ⟨hne,hi⟩⟩

 theorem formulaOutput_member_iff (x replacement : M)
    (hrep : (Tm).val.Evalb ![replacement]) (hclosed : FV replacement = 0)
    (φ : NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d) (name : M) :
    member name (FV (formulaOutput (M := M) (σ := σ) (π := π) (d := d) x replacement φ)) = 1 ↔
      name ≠ x ∧ member name (FV (formulaWord (M := M) (σ := σ) (π := π) (d := d) φ)) = 1 := by
  induction φ with
  | equal s t =>
    rw [formulaOutput,formulaWord,
      equality_occurrences (M := M) σ π d
        (termOutput (M := M) (σ := σ) (d := d) x replacement s)
        (termOutput (M := M) (σ := σ) (d := d) x replacement t)
        (termOutput_member (M := M) (σ := σ) (d := d) π x replacement hrep s) (termOutput_member (M := M) (σ := σ) (d := d) π x replacement hrep t),
      equality_occurrences (M := M) σ π d
        (termWord (M := M) (σ := σ) (d := d) s) (termWord (M := M) (σ := σ) (d := d) t)
        (termWord_member (M := M) (σ := σ) (d := d) π s) (termWord_member (M := M) (σ := σ) (d := d) π t),
      member_append_one,member_append_one,
      termOutput_member_iff (M := M) σ π d x replacement hrep hclosed s name,
      termOutput_member_iff (M := M) σ π d x replacement hrep hclosed t name]
    exact and_or_left.symm
  | relation k p children =>
    rw [formulaOutput,formulaWord,
      relation_occurrences (M := M) σ π d k p (fun i => termOutput (M := M) (σ := σ) (d := d) x replacement (children i))
        (fun i => termOutput_member (M := M) (σ := σ) (d := d) π x replacement hrep (children i)),
      relation_occurrences (M := M) σ π d k p (fun i => termWord (M := M) (σ := σ) (d := d) (children i))
        (fun i => termWord_member (M := M) (σ := σ) (d := d) π (children i)),
      member_gatherTuple (M := M),member_gatherTuple (M := M)]
    constructor
    · rintro ⟨i,hi⟩
      have h := (termOutput_member_iff (M := M) σ π d x replacement hrep hclosed (children i) name).mp hi
      exact ⟨h.1,⟨i,h.2⟩⟩
    · rintro ⟨hne,i,hi⟩
      exact ⟨i,(termOutput_member_iff (M := M) σ π d x replacement hrep hclosed (children i) name).mpr ⟨hne,hi⟩⟩
  | neg body ih =>
    rw [formulaOutput,formulaWord,
      negation_occurrences (M := M) σ π d
        (formulaOutput (M := M) (σ := σ) (π := π) (d := d) x replacement body)
        (formulaOutput_member (M := M) (σ := σ) (π := π) (d := d) x replacement hrep hclosed body),
      negation_occurrences (M := M) σ π d
        (formulaWord (M := M) (σ := σ) (π := π) (d := d) body)
        (formulaWord_member (M := M) (σ := σ) (π := π) (d := d) body)]
    exact ih
  | imp left right il ir =>
    rw [formulaOutput,formulaWord,
      implication_occurrences (M := M) σ π d
        (formulaOutput (M := M) (σ := σ) (π := π) (d := d) x replacement left)
        (formulaOutput (M := M) (σ := σ) (π := π) (d := d) x replacement right)
        (formulaOutput_member (M := M) (σ := σ) (π := π) (d := d) x replacement hrep hclosed left)
        (formulaOutput_member (M := M) (σ := σ) (π := π) (d := d) x replacement hrep hclosed right),
      implication_occurrences (M := M) σ π d
        (formulaWord (M := M) (σ := σ) (π := π) (d := d) left)
        (formulaWord (M := M) (σ := σ) (π := π) (d := d) right)
        (formulaWord_member (M := M) (σ := σ) (π := π) (d := d) left) (formulaWord_member (M := M) (σ := σ) (π := π) (d := d) right),
      member_append_one,member_append_one,il,ir]
    exact and_or_left.symm
  | all y body ih =>
    have hy : variableCarrier.val.Evalb ![(y : M)] := by simp [variableCarrier]
    have hold : FV (formulaWord (M := M) (σ := σ) (π := π) (d := d)
        (NamedFiniteSyntax.Formula.all y body)) =
        delete (y : M) (FV (formulaWord (M := M) (σ := σ) (π := π) (d := d) body)) :=
      quantifier_occurrences (M := M) σ π d (y : M)
        (formulaWord (M := M) (σ := σ) (π := π) (d := d) body) hy
        (formulaWord_member (M := M) (σ := σ) (π := π) (d := d) body)
    by_cases h : (y : M) = x
    · simp only [formulaOutput,h,ite_true]
      have habs : member x (FV (formulaWord (M := M) (σ := σ) (π := π) (d := d)
          (NamedFiniteSyntax.Formula.all y body))) = 0 := by
        rw [hold,member_delete,ite_eq_left h.symm]
      constructor
      · intro hp
        refine ⟨?_,hp⟩
        intro hn
        subst name
        rw [habs] at hp
        exact zero_ne_one hp
      · rintro ⟨_,hp⟩
        exact hp
    · have hnew := quantifier_occurrences (M := M) σ π d (y : M)
        (formulaOutput (M := M) (σ := σ) (π := π) (d := d) x replacement body) hy
        (formulaOutput_member (M := M) (σ := σ) (π := π) (d := d) x replacement hrep hclosed body)
      simp only [formulaOutput,h,ite_false]
      rw [hnew,hold,member_delete,member_delete]
      by_cases hn : name = (y : M)
      · simp only [ite_eq_left hn,zero_ne_one,and_false]
      · simp only [ite_eq_right hn,ih]

/-- An internal numerical list with no named members is zero. The proof
uses its actual nil/adjoin decomposition, not external finiteness. -/
theorem list_eq_zero_of_no_members (list : M) (h : ∀ name : M,member name list ≠ 1) : list = 0 := by
  rcases nil_or_adjoin list with hz | ⟨name,tail,he⟩
  · exact hz
  · exact False.elim (h name (by rw [he]; simp))

 theorem result_sentence (x replacement : M)
    (hrep : (Tm).val.Evalb ![replacement]) (hclosed : FV replacement = 0)
    (φ : NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d)
    (hφ : ∀ name : M,member name (FV (formulaWord (M := M) (σ := σ) (π := π) (d := d) φ)) = 1 → name = x) :
    FV (formulaOutput (M := M) (σ := σ) (π := π) (d := d) x replacement φ) = 0 := by
  apply list_eq_zero_of_no_members
  intro name hn
  have h := (formulaOutput_member_iff (M := M) σ π d x replacement hrep hclosed φ name).mp hn
  exact h.1 (hφ name h.2)

end CategoricalEssentialIncompleteness.V46.NamedArithmeticSubstitutionOccurrences
