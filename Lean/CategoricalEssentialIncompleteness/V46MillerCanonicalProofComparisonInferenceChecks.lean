import CategoricalEssentialIncompleteness.V46MillerCanonicalProofComparisonInference
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.Miller.CanonicalPresentation.Inference
universe v₁ v₂ u₁ u₂
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
variable (E : C ≌ D) {F : C} {F' : D} (e : E.functor.obj F ≅ F') {N : ℕ}
variable (R : RulePresentation F N) (R' : RulePresentation F' N) (h : Data E e R R')
example : R.inference ⋙ (slice E e).functor ≅ (slice E e).functor ⋙ R'.inference := comparison E e R R' h
example (A : Endofunctor.Algebra R.inference) (hA : IsInitial A) :
    IsInitial (mappedAlgebra E e R R' h A) := mappedInitial E e R R' h A hA

example (Q : Over F) (n : Fin (N+1)) :
    (inputIso E e R R' h Q n).hom ≫ pullback.fst _ _ =
      E.functor.map (pullback.fst _ _) ≫ (h.coefficient n).hom :=
  input_fst E e R R' h Q n

example (Q : Over F) (n : Fin (N+1)) :
    (inputIso E e R R' h Q n).hom ≫ pullback.snd _ _ =
      E.functor.map (pullback.snd _ _) ≫
        (ArithmeticIndexedFibers.InferenceTransport.power E Q.left n.val).hom :=
  input_snd E e R R' h Q n

example {Q Q' : Over F} (f : Q ⟶ Q') (n : Fin (N+1)) :
    E.functor.map (R.ruleMap f n) ≫ (inputIso E e R R' h Q' n).hom =
      (inputIso E e R R' h Q n).hom ≫ R'.ruleMap ((slice E e).functor.map f) n :=
  input_natural E e R R' h f n

example {Q Q' : Over F} (f : Q ⟶ Q') :
    (slice E e).functor.map (R.inference.map f) ≫ (component E e R R' h Q').hom =
      (component E e R R' h Q).hom ≫ R'.inference.map ((slice E e).functor.map f) :=
  component_natural E e R R' h f

end CategoricalEssentialIncompleteness.V46.Miller.CanonicalPresentation.Inference
