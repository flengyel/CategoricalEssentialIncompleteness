/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ForkRangeStability

/-! Actual monic-span presentation and every clause of the fork range structure. -/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46
open ForkRangeStability

example : PartialMaps.Par EffectiveFork.Total ≌ EffectiveFork.Object := equivalence
example : Splits Object := inferInstance
example : PCategory Object := inferInstance
example : RecursionCategory.Prodominical Object := inferInstance
example : CategoryTheory.CoprodStruct Object := inferInstance
example : CategoryTheory.HasCoproducts Object := inferInstance
example : RestrictionCoproducts Object := inferInstance
example : HasZeroMorphisms Object := inferInstance
example : RestrictionZero Object := inferInstance
example : WeakChoice Object := inferInstance
example : Ranges Object := inferInstance
example : JoinInverse Object := inferInstance

example {X Y : MonicSpanCategory} (f : X ⟶ Y) :
    equivalence.functor.map (rst f) = rst (equivalence.functor.map f) :=
  preserves_restrictions f

example {X Y : Object} (f : X ⟶ Y) :
    equivalence.inverse.map (rst f) = rst (equivalence.inverse.map f) :=
  inverse_preserves_restrictions f

example {X Y : MonicSpanCategory} (f : X ⟶ Y) :
    equivalence.functor.map (Ranges.range f).hom =
      (Ranges.range (equivalence.functor.map f)).hom := preserves_ranges f

example {X Y : MonicSpanCategory} (f : X.obj ⟶ Y.obj) :
    equivalence.functor.map (PartialMaps.ofTotal f) = f.hom := map_total f

example {X Y : MonicSpanCategory} (s : PartialMaps.Raw X Y) :
    equivalence.functor.map (Ranges.range (PartialMaps.ofSpan s)).hom =
      (Ranges.range s.r.hom).hom := span_image s

example {X Y : Object} (s : PartialSpans.Span X Y) :
    Ranges.range s.value = Ranges.range s.map.hom := span_range s

example {X Y : Object} (f : X ⟶ Y) :
    ∃ s : PartialSpans.Span X Y, s.value = f ∧
      ∀ (Z : Total) (g : Z ⟶ (⟨Y⟩ : Total)),
        Ranges.range (pullback.snd s.map g).hom = Idem.pull g.hom (Ranges.range f) :=
  partial_range_stable f

example {P X Y Z : Total} {p : P ⟶ X} {q : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback p q f g) :
    Ranges.range q.hom = Idem.pull g.hom (Ranges.range f.hom) :=
  EffectiveFork.pullback_image h

example {W X Y Z : Object} (f : W ⟶ X) (g : Y ⟶ Z) :
    (Ranges.range (EffectiveFork.productMap f g)).hom =
      EffectiveFork.productMap (Ranges.range f).hom (Ranges.range g).hom :=
  EffectiveFork.range_product f g

example {X Y : Object} (f : X ⟶ Y) (a b : Idem Y) :
    Idem.pull f (a ⊓ b) = Idem.pull f a ⊓ Idem.pull f b := Idem.pull_inf f a b
example {X Y : Object} (f : X ⟶ Y) (a b : Idem Y) :
    Idem.pull f (a ⊔ b) = Idem.pull f a ⊔ Idem.pull f b := JoinInverse.pull_sup f a b
example {X Y : Object} (f : X ⟶ Y) : Idem.pull f ⊥ = ⊥ := Idem.pull_bot f

example {X Y Z : Object} (f : X ⟶ Y) (g h : Y ⟶ Z) (he : f ≫ g = f ≫ h) :
    (Ranges.range f).hom ≫ g = (Ranges.range f).hom ≫ h := Ranges.agreement f g h he
