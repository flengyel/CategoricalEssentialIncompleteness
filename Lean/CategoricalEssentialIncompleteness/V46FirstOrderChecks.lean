import CategoricalEssentialIncompleteness.V46FirstOrderInference

/-! Explicit first-order rule types and generated-theory inclusions. -/

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46

example {D : Type u} [Category.{v} D] [Regular D] [HasFiniteCoproducts D]
    {V F L S A : D} (logical : L ⟶ F) (sentence : S ⟶ F)
    (axioms : A ⟶ S) (all : V ⨯ F ⟶ F) (imp : F ⨯ F ⟶ F) :
    RulePresentation F 2 :=
  firstOrderRules logical sentence axioms all imp

example {D : Type u} [Category.{v} D] [Regular D] [HasFiniteCoproducts D]
    {V F L S A : D} (logical : L ⟶ F) (sentence : S ⟶ F)
    (axioms : A ⟶ S) (all : V ⨯ F ⟶ F) (imp : F ⨯ F ⟶ F)
    (P : Endofunctor.Algebra (firstOrderRules logical sentence axioms all imp).inference)
    (hP : IsInitial P) :
    ClosedUnder (firstOrderRules logical sentence axioms all imp).inference
      (image.ι P.a.hom) ∧
      ∀ {T : D} (m : T ⟶ F) [Mono m],
        ClosedUnder (firstOrderRules logical sentence axioms all imp).inference m →
          ∃ w : image P.a.hom ⟶ T, w ≫ m = image.ι P.a.hom :=
  firstOrder_least_image logical sentence axioms all imp P hP

example {D : Type u} [Category.{v} D] [Regular D] [HasFiniteCoproducts D]
    {V F L S A A' : D} (logical : L ⟶ F) (sentence : S ⟶ F)
    (axioms : A ⟶ S) (axioms' : A' ⟶ S) (all : V ⨯ F ⟶ F) (imp : F ⨯ F ⟶ F)
    (k : A ⟶ A') (hk : k ≫ axioms' = axioms)
    (P : Endofunctor.Algebra (firstOrderRules logical sentence axioms all imp).inference)
    (hP : IsInitial P)
    (P' : Endofunctor.Algebra (firstOrderRules logical sentence axioms' all imp).inference) :
    imageSubobject (pullback.snd P.a.hom sentence) ≤
      imageSubobject (pullback.snd P'.a.hom sentence) :=
  firstOrder_sentence_image_monotone logical sentence axioms axioms' all imp k hk P hP P'
