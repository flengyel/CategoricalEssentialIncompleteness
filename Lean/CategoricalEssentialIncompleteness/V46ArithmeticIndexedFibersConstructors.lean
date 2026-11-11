/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticIndexedFibersAxioms
public import CategoricalEssentialIncompleteness.V46ArithmeticIndexedFibersParameters
public import CategoricalEssentialIncompleteness.V46ArithmeticIndexedFamily

/-! # Cartesian numeral comparison of the actual Hilbert rule signature

The two ordered MP children retain their own formulas. The comparison
shares only the external numeral and uses the actual axiom pullback.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.ArithmeticIndexedFibers

section ConstantParameter
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {E X Y : D} (ε : ⊤_ D ⟶ E)

def constantParameter (X : D) : X ⟶ E ⨯ X :=
  prod.lift (terminal.from X ≫ ε) (𝟙 X)

omit [FinitaryExtensive D] in
@[reassoc] theorem constantParameter_natural (f : X ⟶ Y) :
    constantParameter ε X ≫ prod.map (𝟙 E) f = f ≫ constantParameter ε Y := by
  apply prod.hom_ext <;> simp [constantParameter]

omit [FinitaryExtensive D] in
/-- Every actual constructor has the cartesian constant-parameter square,
regardless of whether that constructor is monic or computable. -/
theorem constantParameter_pullback (f : X ⟶ Y) :
    IsPullback (constantParameter ε X) f (prod.map (𝟙 E) f) (constantParameter ε Y) := by
  refine IsPullback.mk' (constantParameter_natural ε f) ?_ ?_
  · intro W a b ha _
    have h := congrArg (fun k => k ≫ prod.snd) ha
    simpa only [Category.assoc,constantParameter,prod.lift_snd,Category.comp_id] using h
  · intro W a b h
    refine ⟨a ≫ prod.snd,?_,?_⟩
    · apply prod.hom_ext
      · have he := congrArg (fun k => k ≫ prod.fst) h
        have ht : (a ≫ prod.snd) ≫ terminal.from X = b ≫ terminal.from Y := terminal.hom_ext _ _
        simp only [Category.assoc,prod.map_fst,Category.comp_id,constantParameter,prod.lift_fst] at he ⊢
        have hh : a ≫ prod.snd ≫ terminal.from X ≫ ε = b ≫ terminal.from Y ≫ ε := by
          simpa only [Category.assoc] using congrArg (fun k => k ≫ ε) ht
        exact hh.trans he.symm
      · simp [constantParameter]
    · have he := congrArg (fun k => k ≫ prod.snd) h
      simpa only [Category.assoc,prod.map_snd,constantParameter,prod.lift_snd,Category.comp_id] using he

omit [FinitaryExtensive D] in
/-- Actual supplied maps are compared by proved equations; they need
not reduce definitionally to the constant-parameter expression. -/
theorem constantParameter_natural_of_eq (f : X ⟶ Y)
    (kX : X ⟶ E ⨯ X) (kY : Y ⟶ E ⨯ Y)
    (hX : kX = constantParameter ε X) (hY : kY = constantParameter ε Y) :
    kX ≫ prod.map (𝟙 E) f = f ≫ kY := by
  simpa only [hX,hY] using constantParameter_natural ε f

omit [FinitaryExtensive D] in
theorem constantParameter_pullback_of_eq (f : X ⟶ Y)
    (kX : X ⟶ E ⨯ X) (kY : Y ⟶ E ⨯ Y)
    (hX : kX = constantParameter ε X) (hY : kY = constantParameter ε Y) :
    IsPullback kX f (prod.map (𝟙 E) f) kY := by
  simpa only [hX,hY] using constantParameter_pullback ε f

omit [FinitaryExtensive D] in
theorem constantUnary {V F : D} :
    (prod.snd : V ⨯ F ⟶ F) ≫ constantParameter ε F =
      constantParameter ε (V ⨯ F) ≫ prod.lift prod.fst (prod.snd ≫ prod.snd) := by
  apply prod.hom_ext <;> simp [constantParameter]

omit [FinitaryExtensive D] in
theorem constantBinary {F : D} (imp : F ⨯ F ⟶ F) :
    prod.lift prod.fst imp ≫ prod.map (constantParameter ε F) (constantParameter ε F) =
      constantParameter ε (F ⨯ F) ≫
        prod.lift (prod.lift prod.fst (prod.snd ≫ prod.fst))
          (prod.lift prod.fst (prod.snd ≫ imp)) := by
  apply prod.hom_ext <;> apply prod.hom_ext <;> simp [constantParameter]

/-- Universal binary coproducts assemble the logical and nonlogical
nullary constructor pullbacks. -/
theorem binaryPullback {P₀ P₁ X₀ X₁ Y Z : D}
    {a₀ : P₀ ⟶ X₀} {a₁ : P₁ ⟶ X₁} {b₀ : P₀ ⟶ Y} {b₁ : P₁ ⟶ Y}
    {f₀ : X₀ ⟶ Z} {f₁ : X₁ ⟶ Z} {g : Y ⟶ Z}
    (h₀ : IsPullback a₀ b₀ f₀ g) (h₁ : IsPullback a₁ b₁ f₁ g) :
    IsPullback (coprod.map a₀ a₁) (coprod.desc b₀ b₁) (coprod.desc f₀ f₁) g := by
  let P : WalkingPair → D := fun i => WalkingPair.casesOn i P₀ P₁
  let X : WalkingPair → D := fun i => WalkingPair.casesOn i X₀ X₁
  let a : ∀ i, P i ⟶ X i := fun | .left => a₀ | .right => a₁
  let b : ∀ i, P i ⟶ Y := fun | .left => b₀ | .right => b₁
  let f : ∀ i, X i ⟶ Z := fun | .left => f₀ | .right => f₁
  let c : Cofan X := BinaryCofan.mk (coprod.inl : X₀ ⟶ X₀ ⨿ X₁) coprod.inr
  let d : Cofan P := BinaryCofan.mk (coprod.inl : P₀ ⟶ P₀ ⨿ P₁) coprod.inr
  have hu := FinitaryPreExtensive.isUniversal_finiteCoproducts (c := c) (coprodIsCoprod X₀ X₁)
  have hp := hu.isPullback_of_isColimit_left f (coprod.desc f₀ f₁) g b a
    (by intro i; cases i; exact h₀.flip; exact h₁.flip)
    (d := d) (coprodIsCoprod P₀ P₁) (by intro i; cases i <;> simp [c,f,Cofan.inj,BinaryCofan.mk])
  have hb : Cofan.IsColimit.desc (coprodIsCoprod P₀ P₁) b = coprod.desc b₀ b₁ := by
    apply Cofan.IsColimit.hom_ext (coprodIsCoprod P₀ P₁)
    intro i
    rw [Cofan.IsColimit.fac]
    cases i <;> simp [b,Cofan.inj,BinaryCofan.mk]
  have ha : Cofan.IsColimit.desc (coprodIsCoprod P₀ P₁) (fun i => a i ≫ c.inj i) =
      coprod.map a₀ a₁ := by
    apply Cofan.IsColimit.hom_ext (coprodIsCoprod P₀ P₁)
    intro i
    rw [Cofan.IsColimit.fac]
    cases i <;> simp [a,c,Cofan.inj,BinaryCofan.mk]
  simpa only [hb,ha] using hp.flip
end ConstantParameter

theorem fiberMap_natural (e : ℕ) {X Y : TotalSplit 𝗣𝗔} (f : X ⟶ Y) :
    fiberMap e X ≫ prod.map (𝟙 parameter) f = f ≫ fiberMap e Y :=
  constantParameter_natural_of_eq (numeral e) f (fiberMap e X) (fiberMap e Y)
    (fiberMap_primitive e X) (fiberMap_primitive e Y)

theorem fiberMap_pullback (e : ℕ) {X Y : TotalSplit 𝗣𝗔} (f : X ⟶ Y) :
    IsPullback (fiberMap e X) f (prod.map (𝟙 parameter) f) (fiberMap e Y) :=
  constantParameter_pullback_of_eq (numeral e) f (fiberMap e X) (fiberMap e Y)
    (fiberMap_primitive e X) (fiberMap_primitive e Y)

section ActualSignature
variable (AxPA : Carrier) (e : ℕ)

abbrev singleRules : RulePresentation ArithmeticIndexedFamily.formula 2 :=
  firstOrderRules ArithmeticIndexedFamily.logical ArithmeticIndexedFamily.sentenceInclusion
    (fiberAxioms AxPA e) ArithmeticIndexedFamily.generalization ArithmeticIndexedFamily.implication

/-- The coefficient maps are the actual constant numeral on logical,
generalization and MP instances, and the proved axiom-fiber inclusion. -/
def numeralRuleMap : ∀ i : Fin 3, (singleRules AxPA e).instances i ⟶
    (ArithmeticIndexedFamily.rules AxPA).instances i :=
  Fin.cases (coprod.map (fiberMap e ArithmeticIndexedFamily.logicalParameters) (fiberToFamily AxPA e))
    (Fin.cases (fiberMap e (ArithmeticIndexedFamily.variableObject ⨯ ArithmeticIndexedFamily.formula))
      (Fin.cases (fiberMap e (ArithmeticIndexedFamily.formula ⨯ ArithmeticIndexedFamily.formula))
        (fun i => Fin.elim0 i)))

/-- Every conclusion square is cartesian, including nullary logical and
enumerated nonlogical axioms. -/
theorem numeralRuleConclusion (i : Fin 3) :
    IsPullback (numeralRuleMap AxPA e i) ((singleRules AxPA e).conclusion i)
      ((ArithmeticIndexedFamily.rules AxPA).conclusion i)
      (fiberMap e ArithmeticIndexedFamily.formula) := by
  fin_cases i
  · have hL := fiberMap_pullback e ArithmeticIndexedFamily.logical
    have hA := (axiom_pullback AxPA e).paste_vert
      (fiberMap_pullback e ArithmeticIndexedFamily.sentenceInclusion)
    exact binaryPullback hL hA
  · exact fiberMap_pullback e ArithmeticIndexedFamily.generalization
  · exact fiberMap_pullback e
      (prod.snd : ArithmeticIndexedFamily.formula ⨯ ArithmeticIndexedFamily.formula ⟶ _)

/-- The original ordered premise diagrams, not merely their conclusion
images, identify the numeral restriction of the inference functor. -/
def numeralRuleData : RuleBaseChange.Data (fiberMap e ArithmeticIndexedFamily.formula)
    (singleRules AxPA e) (ArithmeticIndexedFamily.rules AxPA) where
  instanceMap := numeralRuleMap AxPA e
  premises i := by
    fin_cases i
    · exact terminal.hom_ext _ _
    · change prod.snd ≫ fiberMap e ArithmeticIndexedFamily.formula =
        fiberMap e (ArithmeticIndexedFamily.variableObject ⨯ ArithmeticIndexedFamily.formula) ≫
          prod.lift prod.fst (prod.snd ≫ prod.snd)
      simpa only [fiberMap,fiberMap_primitive,constantParameter] using
        (constantUnary (D := TotalSplit 𝗣𝗔) (E := parameter) (numeral e)
          (V := ArithmeticIndexedFamily.variableObject) (F := ArithmeticIndexedFamily.formula))
    · change prod.lift prod.fst ArithmeticIndexedFamily.implication ≫
          prod.map (fiberMap e ArithmeticIndexedFamily.formula) (fiberMap e ArithmeticIndexedFamily.formula) =
        fiberMap e (ArithmeticIndexedFamily.formula ⨯ ArithmeticIndexedFamily.formula) ≫
          prod.lift (prod.lift prod.fst (prod.snd ≫ prod.fst))
            (prod.lift prod.fst (prod.snd ≫ ArithmeticIndexedFamily.implication))
      simpa only [fiberMap,fiberMap_primitive,constantParameter] using
        constantBinary (numeral e) ArithmeticIndexedFamily.implication
  conclusion := numeralRuleConclusion AxPA e

def numeralInferenceComparison :
    (ArithmeticIndexedFamily.rules AxPA).inference ⋙
        Over.pullback (fiberMap e ArithmeticIndexedFamily.formula) ≅
      Over.pullback (fiberMap e ArithmeticIndexedFamily.formula) ⋙ (singleRules AxPA e).inference :=
  RuleBaseChange.comparison _ _ _ (numeralRuleData AxPA e)
end ActualSignature
end CategoricalEssentialIncompleteness.V46.ArithmeticIndexedFibers
