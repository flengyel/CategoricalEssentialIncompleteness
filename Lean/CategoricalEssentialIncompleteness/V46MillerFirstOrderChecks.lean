import CategoricalEssentialIncompleteness.V46MillerFirstOrder
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.Miller
variable (z : Point) (V : Total.CanonicalTotal z) (σ π : ℕ → Total.CanonicalTotal z) (d : ℕ)
local notation "S" => Syntax.canonicalCategoricalSyntax z V σ π d

example : (S).logicalAxioms=
    coprod.desc (coprod.desc (coprod.desc (coprod.desc
      (coprod.desc (coprod.desc (S).hilbertOne (S).hilbertTwo) (S).hilbertThree)
        (S).hilbertInstantiation) (S).hilbertDistribution) (S).hilbertReflexivity) (S).hilbertEquality := rfl

variable {A : Total.CanonicalTotal z}
example (axioms : @Quiver.Hom (Total.CanonicalTotal z) inferInstance A (CategoricalSyntax.sentenceObject (D := Total.CanonicalTotal z) (V := V) (σ := σ) (π := π) (d := d) (S))) : RulePresentation (S).algebra.a.2 2 := @FirstOrder.rules z V σ π d A axioms
example (axioms : @Quiver.Hom (Total.CanonicalTotal z) inferInstance A (CategoricalSyntax.sentenceObject (D := Total.CanonicalTotal z) (V := V) (σ := σ) (π := π) (d := d) (S))) : (@FirstOrder.rules z V σ π d A axioms).instances 0=((S).logicalParameters ⨿ A) := rfl
example (axioms : @Quiver.Hom (Total.CanonicalTotal z) inferInstance A (CategoricalSyntax.sentenceObject (D := Total.CanonicalTotal z) (V := V) (σ := σ) (π := π) (d := d) (S))) : (@FirstOrder.rules z V σ π d A axioms).conclusion 0=
    coprod.desc (S).logicalAxioms (axioms ≫ (S).sentenceInclusion) := rfl
example (axioms : @Quiver.Hom (Total.CanonicalTotal z) inferInstance A (CategoricalSyntax.sentenceObject (D := Total.CanonicalTotal z) (V := V) (σ := σ) (π := π) (d := d) (S))) : (@FirstOrder.rules z V σ π d A axioms).premises 1=
    (prod.snd : V ⨯ (S).algebra.a.2 ⟶ (S).algebra.a.2) := rfl
example (axioms : @Quiver.Hom (Total.CanonicalTotal z) inferInstance A (CategoricalSyntax.sentenceObject (D := Total.CanonicalTotal z) (V := V) (σ := σ) (π := π) (d := d) (S))) : (@FirstOrder.rules z V σ π d A axioms).conclusion 1=(S).quantifierConstructor := rfl
example (axioms : @Quiver.Hom (Total.CanonicalTotal z) inferInstance A (CategoricalSyntax.sentenceObject (D := Total.CanonicalTotal z) (V := V) (σ := σ) (π := π) (d := d) (S))) : (@FirstOrder.rules z V σ π d A axioms).premises 2=
    prod.lift (prod.fst : (S).algebra.a.2 ⨯ (S).algebra.a.2 ⟶ (S).algebra.a.2)
      (S).implicationConstructor := rfl
example (axioms : @Quiver.Hom (Total.CanonicalTotal z) inferInstance A (CategoricalSyntax.sentenceObject (D := Total.CanonicalTotal z) (V := V) (σ := σ) (π := π) (d := d) (S))) : (@FirstOrder.rules z V σ π d A axioms).conclusion 2=
    (prod.snd : (S).algebra.a.2 ⨯ (S).algebra.a.2 ⟶ (S).algebra.a.2) := rfl

example (axioms : @Quiver.Hom (Total.CanonicalTotal z) inferInstance A (CategoricalSyntax.sentenceObject (D := Total.CanonicalTotal z) (V := V) (σ := σ) (π := π) (d := d) (S))) : IsInitial (@FirstOrder.proofAlgebra z V σ π d A axioms) := @FirstOrder.proofInitial z V σ π d A axioms
example (axioms : @Quiver.Hom (Total.CanonicalTotal z) inferInstance A (CategoricalSyntax.sentenceObject (D := Total.CanonicalTotal z) (V := V) (σ := σ) (π := π) (d := d) (S))) : IsPullback (pullback.fst (@FirstOrder.conclusion z V σ π d A axioms) (S).sentenceInclusion)
    (@FirstOrder.sentenceConclusion z V σ π d A axioms) (@FirstOrder.conclusion z V σ π d A axioms)
      (S).sentenceInclusion := @FirstOrder.sentence_isPullback z V σ π d A axioms
example (axioms : @Quiver.Hom (Total.CanonicalTotal z) inferInstance A (CategoricalSyntax.sentenceObject (D := Total.CanonicalTotal z) (V := V) (σ := σ) (π := π) (d := d) (S))) : @FirstOrder.formulaTheory z V σ π d A axioms=
    imageSubobject (@FirstOrder.conclusion z V σ π d A axioms) := rfl
example (axioms : @Quiver.Hom (Total.CanonicalTotal z) inferInstance A (CategoricalSyntax.sentenceObject (D := Total.CanonicalTotal z) (V := V) (σ := σ) (π := π) (d := d) (S))) : @FirstOrder.sentenceTheory z V σ π d A axioms=
    imageSubobject (@FirstOrder.sentenceConclusion z V σ π d A axioms) := rfl
example (axioms : @Quiver.Hom (Total.CanonicalTotal z) inferInstance A (CategoricalSyntax.sentenceObject (D := Total.CanonicalTotal z) (V := V) (σ := σ) (π := π) (d := d) (S))) : @FirstOrder.sentenceTheory z V σ π d A axioms=
    (Subobject.pullback (S).sentenceInclusion).obj (@FirstOrder.formulaTheory z V σ π d A axioms) :=
  @FirstOrder.sentence_theory_pullback z V σ π d A axioms

example (axioms : @Quiver.Hom (Total.CanonicalTotal z) inferInstance A (CategoricalSyntax.sentenceObject (D := Total.CanonicalTotal z) (V := V) (σ := σ) (π := π) (d := d) (S))) : ClosedUnder (@FirstOrder.rules z V σ π d A axioms).inference
    (image.ι (@FirstOrder.conclusion z V σ π d A axioms)) :=
  (@FirstOrder.generated_theory z V σ π d A axioms).1
example (axioms : @Quiver.Hom (Total.CanonicalTotal z) inferInstance A (CategoricalSyntax.sentenceObject (D := Total.CanonicalTotal z) (V := V) (σ := σ) (π := π) (d := d) (S))) {U : Total.CanonicalTotal z} (m : U ⟶ (S).algebra.a.2) [Mono m]
    (hm : ClosedUnder (@FirstOrder.rules z V σ π d A axioms).inference m) :
    ∃ w : image (@FirstOrder.conclusion z V σ π d A axioms) ⟶ U,
      w ≫ m=image.ι (@FirstOrder.conclusion z V σ π d A axioms) :=
  (@FirstOrder.generated_theory z V σ π d A axioms).2.1 m hm
example (axioms : @Quiver.Hom (Total.CanonicalTotal z) inferInstance A (CategoricalSyntax.sentenceObject (D := Total.CanonicalTotal z) (V := V) (σ := σ) (π := π) (d := d) (S))) : ∃ a : A ⟶ image (@FirstOrder.sentenceConclusion z V σ π d A axioms),
    a ≫ image.ι (@FirstOrder.sentenceConclusion z V σ π d A axioms)=axioms :=
  @FirstOrder.sentence_axioms_factor z V σ π d A axioms

example (axioms : @Quiver.Hom (Total.CanonicalTotal z) inferInstance A (CategoricalSyntax.sentenceObject (D := Total.CanonicalTotal z) (V := V) (σ := σ) (π := π) (d := d) (S))) (B : Endofunctor.Algebra (@FirstOrder.rules z V σ π d A axioms).inference) :
    (@FirstOrder.proofFold z V σ π d A axioms B).f.left ≫ B.a.hom=@FirstOrder.conclusion z V σ π d A axioms :=
  @FirstOrder.proofFold_conclusion z V σ π d A axioms B
example (axioms : @Quiver.Hom (Total.CanonicalTotal z) inferInstance A (CategoricalSyntax.sentenceObject (D := Total.CanonicalTotal z) (V := V) (σ := σ) (π := π) (d := d) (S))) (B : Endofunctor.Algebra (@FirstOrder.rules z V σ π d A axioms).inference) :
    (@FirstOrder.proofAlgebra z V σ π d A axioms).str ≫ (@FirstOrder.proofFold z V σ π d A axioms B).f=
      (@FirstOrder.rules z V σ π d A axioms).inference.map (@FirstOrder.proofFold z V σ π d A axioms B).f ≫ B.str :=
  @FirstOrder.proofFold_constructor z V σ π d A axioms B
example (axioms : @Quiver.Hom (Total.CanonicalTotal z) inferInstance A (CategoricalSyntax.sentenceObject (D := Total.CanonicalTotal z) (V := V) (σ := σ) (π := π) (d := d) (S))) (B : Endofunctor.Algebra (@FirstOrder.rules z V σ π d A axioms).inference)
    (f : @FirstOrder.proofAlgebra z V σ π d A axioms ⟶ B) : f=@FirstOrder.proofFold z V σ π d A axioms B :=
  @FirstOrder.proofFold_unique z V σ π d A axioms B f

example (axioms : @Quiver.Hom (Total.CanonicalTotal z) inferInstance A (CategoricalSyntax.sentenceObject (D := Total.CanonicalTotal z) (V := V) (σ := σ) (π := π) (d := d) (S))) : (@FirstOrder.formulaIdem z V σ π d A axioms).hom=
    (Ranges.range (@FirstOrder.conclusion z V σ π d A axioms).hom).hom := rfl
example (axioms : @Quiver.Hom (Total.CanonicalTotal z) inferInstance A (CategoricalSyntax.sentenceObject (D := Total.CanonicalTotal z) (V := V) (σ := σ) (π := π) (d := d) (S))) : ∃ r : (CategoricalSyntax.sentenceObject (D := Total.CanonicalTotal z) (V := V) (σ := σ) (π := π) (d := d) (S)).obj ⟶ (image (@FirstOrder.sentenceConclusion z V σ π d A axioms)).obj,
    (image.ι (@FirstOrder.sentenceConclusion z V σ π d A axioms)).hom ≫ r=𝟙 _ ∧
    r ≫ (image.ι (@FirstOrder.sentenceConclusion z V σ π d A axioms)).hom=rst r ∧
    (@FirstOrder.sentenceIdem z V σ π d A axioms).hom=
      r ≫ (image.ι (@FirstOrder.sentenceConclusion z V σ π d A axioms)).hom :=
  @FirstOrder.sentence_idempotent_represents z V σ π d A axioms

example (A : Subobject (CategoricalSyntax.sentenceObject (D := Total.CanonicalTotal z) (V := V) (σ := σ) (π := π) (d := d) (S))) : A≤FirstOrder.generatedSentence z V σ π d A :=
  FirstOrder.axioms_le_generated z V σ π d A
example (A : Subobject (CategoricalSyntax.sentenceObject (D := Total.CanonicalTotal z) (V := V) (σ := σ) (π := π) (d := d) (S))) :
    FirstOrder.IsSentenceTheory z V σ π d (FirstOrder.generatedSentence z V σ π d A).arrow :=
  FirstOrder.generatedSentence_closed z V σ π d A
example (A B : Subobject (CategoricalSyntax.sentenceObject (D := Total.CanonicalTotal z) (V := V) (σ := σ) (π := π) (d := d) (S))) (hB : FirstOrder.IsSentenceTheory z V σ π d B.arrow)
    (hAB : A≤B) : FirstOrder.generatedSentence z V σ π d A≤B :=
  FirstOrder.generatedSentence_least z V σ π d A B hB hAB
example (A : Subobject (CategoricalSyntax.sentenceObject (D := Total.CanonicalTotal z) (V := V) (σ := σ) (π := π) (d := d) (S))) :
    FirstOrder.generatedSentence z V σ π d (FirstOrder.generatedSentence z V σ π d A)=
      FirstOrder.generatedSentence z V σ π d A := FirstOrder.generatedSentence_idempotent z V σ π d A
example : Monotone (FirstOrder.generatedSentence z V σ π d) := FirstOrder.generatedSentence_monotone z V σ π d
