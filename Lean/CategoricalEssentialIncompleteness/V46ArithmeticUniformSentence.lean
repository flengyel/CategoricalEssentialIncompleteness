import CategoricalEssentialIncompleteness.V46ArithmeticUniformSearchModels
import CategoricalEssentialIncompleteness.V46NamedArithmeticLiteralTotal

/-! # The actual uniform sentence morphism

The source diagonal is chosen once from the joint two-input search. Its total
identity-splitting image is composed with the constructed literal named sentence
morphism. The numerical value comparison is proved for that exact composite.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.RestrictionCategory
open FailureOfComposition FailureOfComposition.TypedProgramCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.LocalConnectedness.PartialFunctions
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.ArithmeticUniformSearch
open NamedArithmeticSignature

/-- One source composite with its proved functor equation. The constructor
below proves every field from f and t; no value law is supplied as input. -/
structure SourceComposite {D : Type u} [Category.{v} D] {X Y Z : D}
    (f : X ⟶ Y) (t : Y ⟶ Z) where
  hom : X ⟶ Z
  hom_eq : hom = f ≫ t
  map_apply : ∀ (H : D ⥤ Type) (x : H.obj X), H.map hom x = H.map t (H.map f x)
  map_value : ∀ (H : D ⥤ Type) (x : H.obj X) (y : H.obj Y) {U : Type}
    (value : H.obj Z → U) (z : U),
    H.map f x = y → value (H.map t y) = z → value (H.map hom x) = z

def sourceComposite {D : Type u} [Category.{v} D] {X Y Z : D}
    (f : X ⟶ Y) (t : Y ⟶ Z) : SourceComposite f t where
  hom := f ≫ t
  hom_eq := rfl
  map_apply H x := H.map_comp_apply f t x
  map_value H x _y _U value _z hf ht :=
    (congrArg value (H.map_comp_apply f t x)).trans
      ((congrArg (fun a => value (H.map t a)) hf).trans ht)

/-- The printed I(g), for an actual source-total g. -/
def totalEndomorphism (g : omegaObject 𝗣𝗔 ⟶ omegaObject 𝗣𝗔) (hg : isTotal g) :
    ArithmeticOmegaComparison.identityOmega 𝗣𝗔 ⟶ ArithmeticOmegaComparison.identityOmega 𝗣𝗔 :=
  ⟨(splittingInclusion (C := CodedProgramCategory 𝗣𝗔)).map g,
    SplitObject.Hom.ext hg⟩

@[simp] theorem totalEndomorphism_underlying (g : omegaObject 𝗣𝗔 ⟶ omegaObject 𝗣𝗔)
    (hg : isTotal g) : (totalEndomorphism g hg).hom.hom = g := rfl

/-- The source composite is constructed once together with its exact
comparison and its functor equation, sharing the category dictionaries. -/
def sentenceData (g : omegaObject 𝗣𝗔 ⟶ omegaObject 𝗣𝗔) (hg : isTotal g)
    (φ : Formula) (hφ : ∀ y, y ∈ φ.freeVariables → y = 0) :
    SourceComposite (D := TotalSplit 𝗣𝗔) (totalEndomorphism g hg)
      (NamedArithmeticLiteralTotal.theta φ hφ) :=
  sourceComposite (totalEndomorphism g hg) (NamedArithmeticLiteralTotal.theta φ hφ)

/-- The actual identity-splitting image followed by the constructed named
sentence map. Its constructor carries a proved comparison with I(g)≫theta. -/
def sentenceFromTotal (g : omegaObject 𝗣𝗔 ⟶ omegaObject 𝗣𝗔) (hg : isTotal g)
    (φ : Formula) (hφ : ∀ y, y ∈ φ.freeVariables → y = 0) :
    @Quiver.Hom (TotalSplit 𝗣𝗔) inferInstance
      (ArithmeticOmegaComparison.identityOmega 𝗣𝗔) NamedArithmeticLiteralTotal.literalSentence :=
  (sentenceData g hg φ hφ).hom

/-- One morphism E→S in B_PA, with no consistency assumption on a fiber. -/
def sentenceMorphism (C C' : Predicate₂) (φ : Formula)
    (hφ : ∀ y, y ∈ φ.freeVariables → y = 0) :
    @Quiver.Hom (TotalSplit 𝗣𝗔) inferInstance
      (ArithmeticOmegaComparison.identityOmega 𝗣𝗔) NamedArithmeticLiteralTotal.literalSentence :=
  sentenceFromTotal (diagonal C C') (diagonal_total C C') φ hφ

section Models
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local notation "F" => SyntacticModel.modelFunctor 𝗣𝗔 M
local notation "G" => PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔 M

/-- An actual source output gives the exact canonical-domain value of I(g). -/
theorem totalEndomorphism_value (g : omegaObject 𝗣𝗔 ⟶ omegaObject 𝗣𝗔)
    (hg : isTotal g) (e n : M) (hn : n ∈ (F).map g e) :
    (G).map (totalEndomorphism g hg) (NamedArithmeticLiteralTotal.omegaPoint 𝗣𝗔 M e) =
      NamedArithmeticLiteralTotal.omegaPoint 𝗣𝗔 M n := by
  let out := (G).map (totalEndomorphism g hg) (NamedArithmeticLiteralTotal.omegaPoint 𝗣𝗔 M e)
  have hr : SyntacticModel.programRelation 𝗣𝗔 M g.val e out.val.val :=
    (PredicateInterpretation.canonicalDomainFunctor_graph 𝗣𝗔 M
      (totalEndomorphism g hg) (NamedArithmeticLiteralTotal.omegaPoint 𝗣𝗔 M e) out).mp rfl
  have hm : out.val.val ∈ (F).map g e :=
    (ArithmeticDiagonalCodes.mem_model_relation M g e out.val.val).mpr hr
  have he : out.val.val = n := Part.mem_unique hm hn
  apply Subtype.ext
  apply Subtype.ext
  exact he

/-- The sentence value law is first proved for an opaque source-total
g. Later specialization does not unfold the parameterized Turing choice. -/
theorem sentenceFromTotal_value (g : omegaObject 𝗣𝗔 ⟶ omegaObject 𝗣𝗔)
    (hg : isTotal g) (φ : Formula) (hφ : ∀ y, y ∈ φ.freeVariables → y = 0)
    (e n : M) (hn : n ∈ (F).map g e) :
    ((G).map (sentenceFromTotal g hg φ hφ)
      (NamedArithmeticLiteralTotal.omegaPoint 𝗣𝗔 M e)).val.val =
        NamedArithmeticFixedSubstitution.value φ n := by
  unfold sentenceFromTotal
  exact (sentenceData g hg φ hφ).map_value (G)
    (NamedArithmeticLiteralTotal.omegaPoint 𝗣𝗔 M e)
    (NamedArithmeticLiteralTotal.omegaPoint 𝗣𝗔 M n)
    (fun s : PredicateInterpretation.CanonicalDomain 𝗣𝗔 M NamedArithmeticLiteralTotal.literalSentence =>
      s.val.val)
    (NamedArithmeticFixedSubstitution.value φ n)
    (totalEndomorphism_value M g hg e n hn)
    (NamedArithmeticLiteralTotal.canonical_value_at φ hφ M n)


/-- A numerical output function of the common source-total g. This is a
choice of values of one already constructed morphism, not source choice by e. -/
def output (C C' : Predicate₂) : M → M :=
  ArithmeticSetModelLaws.totalValue ((F).map (diagonal C C'))
    ((SyntacticModel.modelRangeFunctor 𝗣𝗔 M).map_total
      (diagonal C C') (diagonal_total C C'))

theorem output_mem (C C' : Predicate₂) (e : M) :
    output M C C' e ∈ (F).map (diagonal C C') e :=
  ArithmeticSetModelLaws.totalValue_mem ((F).map (diagonal C C'))
    ((SyntacticModel.modelRangeFunctor 𝗣𝗔 M).map_total
      (diagonal C C') (diagonal_total C C')) e

/-- The same total sentence morphism has exactly the printed code Θ(n)
when n is an actual output of the one source g at e. -/
theorem sentenceMorphism_value_at (C C' : Predicate₂) (φ : Formula)
    (hφ : ∀ y, y ∈ φ.freeVariables → y = 0) (e n : M)
    (hn : n ∈ (F).map (diagonal C C') e) :
    ((G).map (sentenceMorphism C C' φ hφ)
      (NamedArithmeticLiteralTotal.omegaPoint 𝗣𝗔 M e)).val.val =
        NamedArithmeticFixedSubstitution.value φ n :=
  sentenceFromTotal_value M (diagonal C C') (diagonal_total C C') φ hφ e n hn

theorem sentenceMorphism_value (C C' : Predicate₂) (φ : Formula)
    (hφ : ∀ y, y ∈ φ.freeVariables → y = 0) (e : M) :
    ((G).map (sentenceMorphism C C' φ hφ)
      (NamedArithmeticLiteralTotal.omegaPoint 𝗣𝗔 M e)).val.val =
        NamedArithmeticFixedSubstitution.value φ (output M C C' e) :=
  sentenceMorphism_value_at M C C' φ hφ e (output M C C' e) (output_mem M C C' e)

/-- The single source output avoids the two predicates at each fiber
where disjointness and the two diagonal bounds have been proved. -/
theorem output_avoids_at (C C' : Predicate₂) (e : M)
    (hd : ∀ x : M, ¬(C.val.Evalb ![e,x] ∧ C'.val.Evalb ![e,x]))
    (hAlpha : ∀ x : M, ArithmeticDiagonalCodes.alpha.val.Evalb ![x] → C.val.Evalb ![e,x])
    (hBeta : ∀ x : M, ArithmeticDiagonalCodes.beta.val.Evalb ![x] → C'.val.Evalb ![e,x]) :
    ¬ C.val.Evalb ![e,output M C C' e] ∧ ¬ C'.val.Evalb ![e,output M C C' e] :=
  avoids_at M C C' e hd hAlpha hBeta (output M C C' e) (output_mem M C C' e)

end Models
end CategoricalEssentialIncompleteness.V46.ArithmeticUniformSearch
