import CategoricalEssentialIncompleteness.V46ConcreteNamedSubstitutionMap
import CategoricalEssentialIncompleteness.V46ConcreteNamedSubstitutionAll

/-! A literal numerical payload records the original named subtree, its
free-variable list, the substitution result, and an independently computed
free-for Boolean. The formula result uses failure zero or pair(value,one). -/
noncomputable section
local instance primitiveNamedPayloadDecidableEqNat : DecidableEq ℕ := Classical.decEq ℕ
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedSubstitution
open SyntacticSyntax SyntacticSyntax.Coding

def originalGraph : 𝚺₁.Semisentence 2 := .mkSigma “out value. !pi₁Def.val out value”

def occurrencesGraph : 𝚺₁.Semisentence 2 :=
  .mkSigma “out payload. ∃ tail, !pi₂Def.val tail payload ∧ !pi₁Def.val out tail”
def resultGraph : 𝚺₁.Semisentence 2 :=
  .mkSigma “out payload. ∃ tail results, !pi₂Def.val tail payload ∧
    !pi₂Def.val results tail ∧ !pi₁Def.val out results”
def freeForGraph : 𝚺₁.Semisentence 2 :=
  .mkSigma “out payload. ∃ tail results, !pi₂Def.val tail payload ∧
    !pi₂Def.val results tail ∧ !pi₂Def.val out results”
def successfulValueGraph : 𝚺₁.Semisentence 2 :=
  .mkSigma “out payload. ∃ r, !resultGraph.val r payload ∧ !pi₁Def.val out r”
def successGraph : 𝚺₁.Semisentence 2 :=
  .mkSigma “out payload. ∃ r tag, !resultGraph.val r payload ∧ !pi₂Def.val tag r ∧
    ((tag = 1 ∧ out = 1) ∨ (tag ≠ 1 ∧ out = 0))”
def trueGraph : 𝚺₁.Semisentence 2 := .mkSigma “out payload. out = 1”

def payloadGraph : 𝚺₁.Semisentence 5 :=
  .mkSigma “out original fv result freefor. ∃ results tail,
    !pairDef.val results result freefor ∧ !pairDef.val tail fv results ∧
    !pairDef.val out original tail”

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance primitiveNamedPayloadModelDecidableEq : DecidableEq M := Classical.decEq M

def original (v : M) : M := π₁ v
def occurrences (v : M) : M := π₁ (π₂ v)
def result (v : M) : M := π₁ (π₂ (π₂ v))
def freeFor (v : M) : M := π₂ (π₂ (π₂ v))
def successfulValue (v : M) : M := π₁ (result v)
def success (v : M) : M := if π₂ (result v) = 1 then 1 else 0

def payload (old fv res ff : M) : M := ⟪old,⟪fv,⟪res,ff⟫⟫⟫

def ok (v : M) : M := ⟪v,1⟫

@[simp] theorem original_payload (old fv res ff : M) : original (payload old fv res ff) = old := by
  simp [original,payload]
@[simp] theorem occurrences_payload (old fv res ff : M) : occurrences (payload old fv res ff) = fv := by
  simp [occurrences,payload]
@[simp] theorem result_payload (old fv res ff : M) : result (payload old fv res ff) = res := by
  simp [result,payload]
@[simp] theorem freeFor_payload (old fv res ff : M) : freeFor (payload old fv res ff) = ff := by
  simp [freeFor,payload]
@[simp] theorem success_ok (v : M) : success (payload 0 0 (ok v) 0) = 1 := by
  simp [success,ok]

@[simp] theorem originalGraph_eval (out v : M) :
    originalGraph.val.Evalb ![out,v] ↔ out = original v := by simp [originalGraph,original]
@[simp] theorem occurrencesGraph_eval (out v : M) :
    occurrencesGraph.val.Evalb ![out,v] ↔ out = occurrences v := by simp [occurrencesGraph,occurrences]
@[simp] theorem resultGraph_eval (out v : M) :
    resultGraph.val.Evalb ![out,v] ↔ out = result v := by simp [resultGraph,result]
@[simp] theorem freeForGraph_eval (out v : M) :
    freeForGraph.val.Evalb ![out,v] ↔ out = freeFor v := by simp [freeForGraph,freeFor]
@[simp] theorem successfulValueGraph_eval (out v : M) :
    successfulValueGraph.val.Evalb ![out,v] ↔ out = successfulValue v := by
  simp [successfulValueGraph,successfulValue]
@[simp] theorem successGraph_eval (out v : M) :
    successGraph.val.Evalb ![out,v] ↔ out = success v := by
  by_cases h : π₂ (result v) = 1 <;> simp [successGraph,success,h]
omit [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] in
@[simp] theorem trueGraph_eval (out v : M) : trueGraph.val.Evalb ![out,v] ↔ out = 1 := by simp [trueGraph]
@[simp] theorem payloadGraph_eval (out old fv res ff : M) :
    payloadGraph.val.Evalb ![out,old,fv,res,ff] ↔ out = payload old fv res ff := by
  simp [payloadGraph,payload]

instance original_defined : 𝚺₁-Function₁ (original : M → M) via originalGraph := .mk fun v => by
  have hv : ![v 0,v 1] = v := (Matrix.fun_eq_vec_two v).symm
  simpa [hv] using originalGraph_eval (v 0) (v 1)
instance occurrences_defined : 𝚺₁-Function₁ (occurrences : M → M) via occurrencesGraph := .mk fun v => by
  have hv : ![v 0,v 1] = v := (Matrix.fun_eq_vec_two v).symm
  simpa [hv] using occurrencesGraph_eval (v 0) (v 1)
instance result_defined : 𝚺₁-Function₁ (result : M → M) via resultGraph := .mk fun v => by
  have hv : ![v 0,v 1] = v := (Matrix.fun_eq_vec_two v).symm
  simpa [hv] using resultGraph_eval (v 0) (v 1)
instance freeFor_defined : 𝚺₁-Function₁ (freeFor : M → M) via freeForGraph := .mk fun v => by
  have hv : ![v 0,v 1] = v := (Matrix.fun_eq_vec_two v).symm
  simpa [hv] using freeForGraph_eval (v 0) (v 1)
instance successfulValue_defined : 𝚺₁-Function₁ (successfulValue : M → M) via successfulValueGraph := .mk fun v => by
  have hv : ![v 0,v 1] = v := (Matrix.fun_eq_vec_two v).symm
  simpa [hv] using successfulValueGraph_eval (v 0) (v 1)
instance success_defined : 𝚺₁-Function₁ (success : M → M) via successGraph := .mk fun v => by
  have hv : ![v 0,v 1] = v := (Matrix.fun_eq_vec_two v).symm
  simpa [hv] using successGraph_eval (v 0) (v 1)
omit [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] in
instance true_defined : 𝚺₁-Function₁ (fun _ : M => (1 : M)) via trueGraph := .mk fun v => by
  have hv : ![v 0,v 1] = v := (Matrix.fun_eq_vec_two v).symm
  simpa [hv] using trueGraph_eval (v 0) (v 1)

end Models

open SyntacticSyntax.NatVectors

theorem original_primrec : Primrec (original : ℕ → ℕ) := pi1_primrec
theorem occurrences_primrec : Primrec (occurrences : ℕ → ℕ) := pi1_primrec.comp pi2_primrec
theorem result_primrec : Primrec (result : ℕ → ℕ) := pi1_primrec.comp (pi2_primrec.comp pi2_primrec)
theorem freeFor_primrec : Primrec (freeFor : ℕ → ℕ) := pi2_primrec.comp (pi2_primrec.comp pi2_primrec)
theorem successfulValue_primrec : Primrec (successfulValue : ℕ → ℕ) := pi1_primrec.comp result_primrec
theorem success_primrec : Primrec (success : ℕ → ℕ) :=
  Primrec.ite (Primrec.eq.comp (pi2_primrec.comp result_primrec) (Primrec.const 1))
    (Primrec.const 1) (Primrec.const 0)

theorem payload_primrec : Primrec (fun p : ℕ × ℕ × ℕ × ℕ => payload p.1 p.2.1 p.2.2.1 p.2.2.2) :=
  pair_primrec.comp Primrec.fst (pair_primrec.comp (Primrec.fst.comp Primrec.snd)
    (pair_primrec.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))

end CategoricalEssentialIncompleteness.V46.ConcreteNamedSubstitution
