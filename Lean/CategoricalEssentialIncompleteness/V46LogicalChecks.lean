import CategoricalEssentialIncompleteness.V46LogicalComparison

/-! Explicit types for interpreted theories and the split-source comparison. -/

noncomputable section

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.RestrictionCategory
open CategoryTheory.Limits (HasZeroMorphisms)
open CategoryTheory.CoprodStruct CategoryTheory.HasCoproducts
open PCategoryStruct (nearProd)
open CategoricalEssentialIncompleteness.LocalConnectedness

section Interpretation

variable {C : Type u₁} [Category.{v₁} C] [RestrictionCategory C]
variable [HasZeroMorphisms C] [RestrictionZero C] [Ranges C]

example {P T V S : C} (c : P ⟶ S) (m : T ⟶ S) (r : S ⟶ T)
    (hm : isTotal m) (hmr : m ≫ r = 𝟙 T)
    (hrm : r ≫ m = (Ranges.range c).hom)
    (k : P ⟶ V) (v : V ⟶ S) (q : S ⟶ V) (hv : isTotal v)
    (hvq : v ≫ q = 𝟙 V) (hqv : q ≫ v = rst q) (hc : c = k ≫ v) :
    ∃ w : T ⟶ V, isTotal w ∧ w ≫ v = m :=
  theory_inclusion_factors c m r hm hmr hrm k v q hv hvq hqv hc

example {P V S : C} (c : P ⟶ S) (k : P ⟶ V) (v : V ⟶ S)
    (d : Idem S) (hc : c = k ≫ v) (hv : v ≫ d.hom = v)
    (ν : S ⟶ S) (hd : d ⊓ Idem.pull ν d = ⊥) :
    Ranges.range c ⊓ Idem.pull ν (Ranges.range c) = ⊥ :=
  consistency_of_sound_factorization c k v d hc hv ν hd

end Interpretation

section LogicalComparison

variable {R : Type u₁} {A : Type u₂} [Category.{v₁} R] [Category.{v₂} A]
variable [PCategoryStruct R] [PCategory R] [RestrictionCategory A]
variable [HasZeroMorphisms R] [RestrictionZero R]
variable [HasZeroMorphisms A] [RestrictionZero A]
variable [CoprodStruct R] [CategoryTheory.HasCoproducts R] [RestrictionCoproducts R]
variable [CoprodStruct A] [CategoryTheory.HasCoproducts A] [RestrictionCoproducts A]
variable [Ranges R] [Ranges A] [TotalJoinInverse A] [Splits A]

example (F : RangeFunctor R A) {U : R}
    (τ : nearProd U U ⟶ U) (hτ : RecursionCategory.IsTuringMorphism τ)
    (b : U ≅ coprod U U) (hU : F.toFunctor.map (𝟙 U) ≠ 0) :
    let choices := V46.normalizedTargetSplitting F
    let G := V46.chosenSplitRangeFunctor F choices
    let σ := V46.chosenSplitExtensionInclusionIso F choices
    ∀ {S : SplitObject R} (θ : (splittingInclusion (C := R)).obj U ⟶ S),
      isTotal θ → ∀ (ν : S ⟶ S), isTotal ν → ∀ tA : Idem S,
      G.mapIdem tA ⊓ Idem.pull (G.toFunctor.map ν) (G.mapIdem tA) = ⊥ →
      F.mapIdem (diagonal0 τ b) ≤
        Idem.pull (σ.inv.app U ≫ G.toFunctor.map θ) (G.mapIdem tA) →
      F.mapIdem (diagonal1 τ b) ≤
        Idem.pull (σ.inv.app U ≫ G.toFunctor.map θ)
          (Idem.pull (G.toFunctor.map ν) (G.mapIdem tA)) →
      ∀ s : F.toFunctor.obj U ⟶ coprod (F.toFunctor.obj U) (F.toFunctor.obj U),
      Idem.pull s (summand0 (F.toFunctor.obj U) (F.toFunctor.obj U)) =
        Idem.pull (σ.inv.app U ≫ G.toFunctor.map θ)
          (Idem.pull (G.toFunctor.map ν) (G.mapIdem tA)) →
      Idem.pull s (summand1 (F.toFunctor.obj U) (F.toFunctor.obj U)) =
        Idem.pull (σ.inv.app U ≫ G.toFunctor.map θ) (G.mapIdem tA) →
      ∀ ℓ : U ⟶ coprod U U,
      F.toFunctor.map ℓ = s ≫ (F.comparison U U).hom →
      ∃ g : U ⟶ U, isTotal g ∧
        Idem.pull (G.toFunctor.map ((splittingInclusion (C := R)).map g ≫ θ))
          (G.mapIdem tA) = ⊥ ∧
        Idem.pull (G.toFunctor.map ((splittingInclusion (C := R)).map g ≫ θ))
          (Idem.pull (G.toFunctor.map ν) (G.mapIdem tA)) = ⊥ ∧
        G.mapIdem tA ⊔ Idem.pull (G.toFunctor.map ν) (G.mapIdem tA) ≠ ⊤ ∧
        tA ⊔ Idem.pull ν tA ≠ ⊤ := by
  dsimp only
  intro S θ hθ ν _hν tA ht ha0 ha1 s hs0 hs1 ℓ hℓ
  exact logical_comparison F (V46.normalizedTargetSplitting F) τ hτ b hU
    θ hθ ν tA ht ha0 ha1 s hs0 hs1 ℓ hℓ

end LogicalComparison
