import CategoricalEssentialIncompleteness.V46ConcreteNamedSubstitutionAlgorithm

/-! Explicit PA-model and standard primitive-recursion statement checks. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Coding
open CategoricalEssentialIncompleteness.V46.ConcreteNamedSubstitution
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
example (V : Carrier) (σ π : ℕ → Carrier) (d : ℕ) :
    Primrec (fun p : ℕ × ℕ × ℕ => substitutionResult V σ π d p.1 p.2.1 p.2.2) :=
  substitutionResult_primrec V σ π d
example (V : Carrier) (σ π : ℕ → Carrier) (d : ℕ) :
    Primrec (fun p : ℕ × ℕ × ℕ => substitutionFreeFor V σ π d p.1 p.2.1 p.2.2) :=
  substitutionFreeFor_primrec V σ π d

example (V : Carrier) (σ π : ℕ → Carrier) (d : ℕ) :
    Nat.Primrec (codedSubstitutionResult V σ π d : ℕ → ℕ) :=
  codedSubstitutionResult_natPrimrec V σ π d
example (V : Carrier) (σ π : ℕ → Carrier) (d : ℕ) :
    Nat.Primrec (codedSubstitutionFreeFor V σ π d : ℕ → ℕ) :=
  codedSubstitutionFreeFor_natPrimrec V σ π d
example (V : Carrier) (σ π : ℕ → Carrier) (d : ℕ) (out x t word : M) :
    (substitutionPayloadGraph V σ π d).val.Evalb ![out,x,t,word] ↔
      out = substitutionPayload V σ π d x t word :=
  substitutionPayloadGraph_eval V σ π d out x t word
