import CategoricalEssentialIncompleteness.V46SyntacticSearch
import CategoricalEssentialIncompleteness.V46ExponentialPairing
import CategoricalEssentialIncompleteness.V46PrintedObjectCodingModels
import CategoricalEssentialIncompleteness.V46ParameterizedTuringDiagonal

/-! # Joint functional search for the uniform arithmetic construction

The relation may have two outputs in an inconsistent fiber. The selected
program is nevertheless functional. Its soundness and domain are proved
without a disjointness hypothesis; exactness is used only at a supplied
disjoint parameter fiber.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.RestrictionCategory
open CategoryTheory.CoprodStruct CategoryTheory.HasCoproducts
open PCategoryStruct
open FailureOfComposition FailureOfComposition.ProgramGraph FailureOfComposition.ProofSearch FailureOfComposition.ConcreteEvaluator
open FailureOfComposition.TypedProgramCategory FailureOfComposition.TypedRecursionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.ArithmeticUniformSearch

abbrev Predicate₂ := 𝚺₁.Semisentence 2

/-- These are precisely the printed reversed even/odd output clauses. -/
def reversedRelation (C C' : Predicate₂) : 𝚺₁.Semisentence 3 :=
  .mkSigma “e x z. (!C.val e x ∧ z = 2 * x + 1) ∨ (!C'.val e x ∧ z = 2 * x)”

/-- A single numerical input uses the proved exponential product code. -/
def inputGraph (C C' : Predicate₂) : Graph :=
  let Pair := ExponentialPairing.graph
  let R := reversedRelation C C'
  .mkSigma “w z. ∃ e x, !Pair.val w e x ∧ !R.val e x z”

def index (C C' : Predicate₂) : ℕ := SyntacticSearch.searchIndex (inputGraph C C')

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

@[simp] theorem reversedRelation_eval (C C' : Predicate₂) (e x z : M) :
    (reversedRelation C C').val.Evalb ![e,x,z] ↔
      (C.val.Evalb ![e,x] ∧ z = 2*x+1) ∨ (C'.val.Evalb ![e,x] ∧ z = 2*x) := by
  simp [reversedRelation]

@[simp] theorem inputGraph_eval (C C' : Predicate₂) (w z : M) :
    (inputGraph C C').val.Evalb ![w,z] ↔
      ∃ e x : M, w = ExponentialPairing.code e x ∧
        (reversedRelation C C').val.Evalb ![e,x,z] := by
  simp [inputGraph]

/-- The input comparison holds at arbitrary internal PA-model entries. -/
theorem inputGraph_code (C C' : Predicate₂) (e x z : M) :
    (inputGraph C C').val.Evalb ![ExponentialPairing.code e x,z] ↔
      (reversedRelation C C').val.Evalb ![e,x,z] := by
  rw [inputGraph_eval]
  constructor
  · rintro ⟨a,b,he,hR⟩
    obtain ⟨rfl,rfl⟩ := ExponentialPairing.code_injective he
    exact hR
  · intro hR
    exact ⟨e,x,rfl,hR⟩

theorem relation_domain (C C' : Predicate₂) (e x : M) :
    (∃ z : M, (reversedRelation C C').val.Evalb ![e,x,z]) ↔
      C.val.Evalb ![e,x] ∨ C'.val.Evalb ![e,x] := by
  simp only [reversedRelation_eval]
  constructor
  · rintro ⟨z,h | h⟩
    · exact Or.inl h.1
    · exact Or.inr h.1
  · rintro (h | h)
    · exact ⟨2*x+1,Or.inl ⟨h,rfl⟩⟩
    · exact ⟨2*x,Or.inr ⟨h,rfl⟩⟩

/-- Soundness is unconditional, including inconsistent fibers. -/
theorem search_sound_at (C C' : Predicate₂) (e x z : M)
    (h : (eventualGraph (index C C')).val.Evalb ![ExponentialPairing.code e x,z]) :
    (reversedRelation C C').val.Evalb ![e,x,z] :=
  (inputGraph_code C C' e x z).mp
    (SyntacticSearch.search_sound_in_model (inputGraph C C') _ _ h)

/-- The entire domain is C or C'; no global functionality of R is used. -/
theorem search_domain_at (C C' : Predicate₂) (e x : M) :
    (∃ z : M, (eventualGraph (index C C')).val.Evalb ![ExponentialPairing.code e x,z]) ↔
      C.val.Evalb ![e,x] ∨ C'.val.Evalb ![e,x] := by
  rw [index,SyntacticSearch.search_domain_in_model (inputGraph C C')]
  exact (exists_congr (fun z => inputGraph_code C C' e x z)).trans (relation_domain C C' e x)

/-- The program graph is functional even when the searched relation is
not. This is the production evaluator's proved output uniqueness. -/
theorem search_functional (C C' : Predicate₂) (w y z : M)
    (hy : (eventualGraph (index C C')).val.Evalb ![w,y])
    (hz : (eventualGraph (index C C')).val.Evalb ![w,z]) : y = z :=
  eventualGraph_output_unique (index C C') w y z hy hz

/-- Only one particular parameter fiber is required to be disjoint. -/
theorem relation_functional_at (C C' : Predicate₂) (e : M)
    (hd : ∀ x : M, ¬ (C.val.Evalb ![e,x] ∧ C'.val.Evalb ![e,x]))
    (x y z : M) (hy : (reversedRelation C C').val.Evalb ![e,x,y])
    (hz : (reversedRelation C C').val.Evalb ![e,x,z]) : y = z := by
  rw [reversedRelation_eval] at hy hz
  rcases hy with ⟨hc,rfl⟩ | ⟨hc',rfl⟩
  · rcases hz with ⟨_,rfl⟩ | ⟨hc',_⟩
    · rfl
    · exact False.elim (hd x ⟨hc,hc'⟩)
  · rcases hz with ⟨hc,_⟩ | ⟨_,rfl⟩
    · exact False.elim (hd x ⟨hc,hc'⟩)
    · rfl

/-- Exact output is proved locally from domain plus soundness. The
program and its index have already been chosen for every parameter. -/
theorem search_exact_at (C C' : Predicate₂) (e : M)
    (hd : ∀ x : M, ¬ (C.val.Evalb ![e,x] ∧ C'.val.Evalb ![e,x])) (x z : M) :
    (eventualGraph (index C C')).val.Evalb ![ExponentialPairing.code e x,z] ↔
      (reversedRelation C C').val.Evalb ![e,x,z] := by
  constructor
  · exact search_sound_at C C' e x z
  · intro hR
    obtain ⟨y,hy⟩ := (search_domain_at C C' e x).mpr ((relation_domain C C' e x).mp ⟨z,hR⟩)
    have he := relation_functional_at C C' e hd x y z (search_sound_at C C' e x y hy) hR
    exact he ▸ hy

end Models

/-- Pairing is stated by its graph, so the printed PA statements have
only the original arithmetic-language symbols. -/
def soundSentence (C C' : Predicate₂) : ArithmeticSentence :=
  let Pair := ExponentialPairing.graph
  let G := eventualGraph (index C C')
  let R := reversedRelation C C'
  “∀ e x w z, !Pair.val w e x → !G.val w z → !R.val e x z”

def domainSentence (C C' : Predicate₂) : ArithmeticSentence :=
  let Pair := ExponentialPairing.graph
  let G := eventualGraph (index C C')
  “∀ e x w, !Pair.val w e x → ((∃ z, !G.val w z) ↔ (!C.val e x ∨ !C'.val e x))”

theorem sound_PA (C C' : Predicate₂) : 𝗣𝗔 ⊢ soundSentence C C' := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  have h : ∀ e x w z : M, ExponentialPairing.graph.val.Evalb ![w,e,x] →
      (eventualGraph (index C C')).val.Evalb ![w,z] →
      (reversedRelation C C').val.Evalb ![e,x,z] := by
    intro e x w z hw hz
    have he := (ExponentialPairing.graph_eval w e x).mp hw
    subst w
    exact search_sound_at C C' e x z hz
  simpa [models_iff,soundSentence] using h

theorem domain_PA (C C' : Predicate₂) : 𝗣𝗔 ⊢ domainSentence C C' := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  have h : ∀ e x w : M, ExponentialPairing.graph.val.Evalb ![w,e,x] →
      ((∃ z : M, (eventualGraph (index C C')).val.Evalb ![w,z]) ↔
        C.val.Evalb ![e,x] ∨ C'.val.Evalb ![e,x]) := by
    intro e x w hw
    have he := (ExponentialPairing.graph_eval w e x).mp hw
    subst w
    exact search_domain_at C C' e x
  simpa [models_iff,domainSentence] using h

/-- One actual source morphism is chosen before any e or consistency
hypothesis. Its numerical output uses the fixed parity coding. -/
def numberSearch (C C' : Predicate₂) : omegaObject 𝗣𝗔 ⟶ omegaObject 𝗣𝗔 :=
  arrowOfIndex 𝗣𝗔 .omega .omega (index C C')

def lift (C C' : Predicate₂) : nearProd (omegaObject 𝗣𝗔) (omegaObject 𝗣𝗔) ⟶
    coprod (omegaObject 𝗣𝗔) (omegaObject 𝗣𝗔) :=
  (PrintedObjectCoding.omegaProductIso 𝗣𝗔).hom ≫ numberSearch C C' ≫ (omegaCoprodIso 𝗣𝗔).inv

/-- The actual source lift, conjugated to the printed exponential input
and parity output coordinates, is the selected numerical search program.
This is source-category equality, before choosing a model or a fiber. -/
theorem lift_printed_coordinates (C C' : Predicate₂) :
    (PrintedObjectCoding.omegaProductIso 𝗣𝗔).inv ≫ lift C C' ≫
      (omegaCoprodIso 𝗣𝗔).hom = numberSearch C C' := by
  calc
    _ = ((PrintedObjectCoding.omegaProductIso 𝗣𝗔).inv ≫
          (PrintedObjectCoding.omegaProductIso 𝗣𝗔).hom) ≫ numberSearch C C' ≫
          ((omegaCoprodIso 𝗣𝗔).inv ≫ (omegaCoprodIso 𝗣𝗔).hom) := by
      simp only [lift,Category.assoc]
    _ = numberSearch C C' := by
      rw [Iso.inv_hom_id,Iso.inv_hom_id,Category.id_comp,Category.comp_id]

/-- This is a single chosen source morphism, rather than a pointwise
choice of a different diagonalization in every numeral fiber. -/
def diagonal (C C' : Predicate₂) : omegaObject 𝗣𝗔 ⟶ omegaObject 𝗣𝗔 :=
  Classical.choose (ParameterizedTuringDiagonal.arithmetic_parameter_diagonal (lift C C'))

theorem diagonal_total (C C' : Predicate₂) : isTotal (diagonal C C') :=
  (Classical.choose_spec (ParameterizedTuringDiagonal.arithmetic_parameter_diagonal (lift C C'))).1

theorem diagonal_equation (C C' : Predicate₂) :
    diagonal C C' ≫ diag (omegaObject 𝗣𝗔) ≫ ArithmeticDiagonalCodes.sourceTau ≫
      (omegaCoprodIso 𝗣𝗔).inv =
        partialPairing (𝟙 (omegaObject 𝗣𝗔)) (diagonal C C') ≫ lift C C' :=
  (Classical.choose_spec (ParameterizedTuringDiagonal.arithmetic_parameter_diagonal (lift C C'))).2

end CategoricalEssentialIncompleteness.V46.ArithmeticUniformSearch
