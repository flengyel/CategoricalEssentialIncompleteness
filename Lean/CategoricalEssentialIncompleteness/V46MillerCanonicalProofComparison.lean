/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerCanonicalProofComparisonInference
public import Mathlib.Tactic.FinCases

/-! # The canonical Γ derivation algebra and generated sentence image

The target is the successful derivation algebra for S2.logicalRules on the
transported arbitrary Γ sentence subobject. Its comparison with the mapped
original word proof algebra is constructed from the two initial algebras.
The final image comparison includes their conclusions and sentence
pullbacks. No conclusion-image comparison is an input.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.Miller.CanonicalPresentation

private theorem formulaPower_one_hom {C D : Type} [Category.{0} C] [Category.{0} D]
    [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
    (e : C ≌ D) {X : C} {Y : D} (i : e.functor.obj X ≅ Y) :
    (Inference.formulaPower e i 1).hom=i.hom := by
  simp only [Inference.formulaPower,ArithmeticIndexedFibers.InferenceTransport.power,
    Inference.powerIso,Iso.trans_hom,Iso.refl_hom,finitePowerMap,Category.id_comp]

private theorem formulaPower_two_hom {C D : Type} [Category.{0} C] [Category.{0} D]
    [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
    (e : C ≌ D) {X : C} {Y : D} (i : e.functor.obj X ≅ Y) :
    (Inference.formulaPower e i 2).hom=(SyntaxOptionTransport.productIso e i i).hom := by
  simp only [Inference.formulaPower,ArithmeticIndexedFibers.InferenceTransport.power,
    Inference.powerIso,SyntaxOptionTransport.productIso,Iso.trans_hom,Iso.refl_hom,
    asIso_hom,prod.mapIso_hom,finitePowerMap,finitePower,prod.map_id_id,Category.comp_id]

private theorem inverse_iso_square {C : Type} [Category.{0} C] {X Y X' Y' : C}
    (i : X ≅ X') (j : Y ≅ Y') (f : X ⟶ Y) (g : X' ⟶ Y')
    (h : f ≫ j.hom=i.hom ≫ g) : i.inv ≫ f=g ≫ j.inv := by
  apply (cancel_mono j.hom).mp
  calc
    (i.inv ≫ f) ≫ j.hom=i.inv ≫ (f ≫ j.hom) := Category.assoc _ _ _
    _=i.inv ≫ (i.hom ≫ g) := congrArg (fun k => i.inv ≫ k) h
    _=g := by rw [← Category.assoc,i.inv_hom_id,Category.id_comp]
    _=(g ≫ j.inv) ≫ j.hom := by rw [Category.assoc,j.inv_hom_id,Category.comp_id]

variable (a : Point) (σ π : ℕ → Carrier) (d : ℕ)
variable (Γ : Set ℕ) (hΓ : Uniform.Enumerable (Uniform.Family.ofPoint a) (· ∈ Γ))
local notation "P" => Uniform.Family.ofPoint a
local notation "E" => Total.pointPresentation a
local notation "V" => (NamedPostfixEncoding.variableCarrier : PredicateCategory 𝗣𝗔)
local notation "S₁" => NamedProofImage.syntaxData (P) σ π d
local notation "S₂" => NamedSyntaxComparison.canonicalPresentedSyntax a (V) σ π d
local notation "R₁" => NamedProofImage.rules (P) σ π d Γ hΓ
local notation "ifm" => formulaIso a (V) σ π d

def canonicalRules : RulePresentation (S₂).algebra.a.2 2 :=
  (S₂).logicalRules (canonicalAxioms a σ π d Γ hΓ)

def ruleCoefficient : ∀ n : Fin 3, (E).functor.obj ((R₁).instances n) ≅
    (canonicalRules a σ π d Γ hΓ).instances n :=
  Fin.cases
    (SyntaxOperationsTransport.sumInputIso (E) (logicalParametersIso a (V) σ π d) (Iso.refl _))
    (Fin.cases (SyntaxOptionTransport.productIso (E) (nameIso a (V)) (ifm))
      (Fin.cases (formulaPairIso a (V) σ π d) (fun n => Fin.elim0 n)))

theorem rule_premises (n : Fin 3) :
    (E).functor.map ((R₁).premises n) ≫ (Inference.formulaPower (E) (ifm) n.val).hom =
      (ruleCoefficient a σ π d Γ hΓ n).hom ≫ (canonicalRules a σ π d Γ hΓ).premises n := by
  fin_cases n
  · exact terminalIsTerminal.hom_ext _ _
  · rw [formulaPower_one_hom]
    change (E).functor.map prod.snd ≫ (ifm).hom =
      (SyntaxOptionTransport.productIso (E) (nameIso a (V)) (ifm)).hom ≫ prod.snd
    exact square_snd («E» := (E)) _ _
  · rw [formulaPower_two_hom]
    change (E).functor.map (prod.lift prod.fst (S₁).implicationConstructor) ≫
        (SyntaxOptionTransport.productIso (E) (ifm) (ifm)).hom =
      (SyntaxOptionTransport.productIso (E) (ifm) (ifm)).hom ≫
        prod.lift prod.fst (S₂).implicationConstructor
    exact square_lift («E» := (E)) (square_fst («E» := (E)) _ _) (implication_comparison a (V) σ π d)

theorem axiom_formula_comparison :
    (E).functor.map (NamedProofImage.axioms (P) σ π d Γ hΓ ≫ (S₁).sentenceInclusion) ≫ (ifm).hom =
      (canonicalAxioms a σ π d Γ hΓ) ≫ (S₂).sentenceInclusion := by
  let ax := NamedProofImage.axioms (P) σ π d Γ hΓ
  have hm := congrArg (fun f => f ≫ (ifm).hom) ((E).functor.map_comp ax (S₁).sentenceInclusion)
  have hi := congrArg (fun f => (E).functor.map ax ≫ f)
    (mappedSentenceIso_inclusion a (V) σ π d).symm
  exact hm.trans ((Category.assoc _ _ _).trans (hi.trans (Category.assoc _ _ _).symm))

theorem rule_conclusion (n : Fin 3) :
    (E).functor.map ((R₁).conclusion n) ≫ (ifm).hom =
      (ruleCoefficient a σ π d Γ hΓ n).hom ≫ (canonicalRules a σ π d Γ hΓ).conclusion n := by
  fin_cases n
  · change (E).functor.map (coprod.desc (S₁).logicalAxioms
        (NamedProofImage.axioms (P) σ π d Γ hΓ ≫ (S₁).sentenceInclusion)) ≫ (ifm).hom =
      (ruleCoefficient a σ π d Γ hΓ 0).hom ≫
        coprod.desc (S₂).logicalAxioms (canonicalAxioms a σ π d Γ hΓ ≫ (S₂).sentenceInclusion)
    apply square_desc («E» := (E))
    · exact logicalAxioms_comparison a (V) σ π d
    · simpa only [Iso.refl_hom, Category.id_comp] using axiom_formula_comparison a σ π d Γ hΓ
  · exact quantifier_comparison a (V) σ π d
  · exact square_snd («E» := (E)) _ _

def ruleData : Inference.Data (E) (ifm) (R₁) (canonicalRules a σ π d Γ hΓ) where
  coefficient := ruleCoefficient a σ π d Γ hΓ
  premises := rule_premises a σ π d Γ hΓ
  conclusion := rule_conclusion a σ π d Γ hΓ

/-- The inference comparison includes each prescribed ordered premise pullback, its
original rule label and the formula conclusion. -/
def inferenceIso : (R₁).inference ⋙ (Inference.slice (E) (ifm)).functor ≅
    (Inference.slice (E) (ifm)).functor ⋙ (canonicalRules a σ π d Γ hΓ).inference :=
  Inference.comparison (E) (ifm) (R₁) (canonicalRules a σ π d Γ hΓ) (ruleData a σ π d Γ hΓ)

def canonicalProofAlgebra : Endofunctor.Algebra (canonicalRules a σ π d Γ hΓ).inference :=
  Derivation.Canonical.derivationAlgebra a (canonicalRules a σ π d Γ hΓ)

def canonicalProofInitial : IsInitial (canonicalProofAlgebra a σ π d Γ hΓ) :=
  Derivation.Canonical.derivationInitial a (canonicalRules a σ π d Γ hΓ)

def mappedProofAlgebra : Endofunctor.Algebra (canonicalRules a σ π d Γ hΓ).inference :=
  Inference.mappedAlgebra (E) (ifm) (R₁) (canonicalRules a σ π d Γ hΓ)
    (ruleData a σ π d Γ hΓ) (NamedProofImage.proofAlgebra (P) σ π d Γ hΓ)

def mappedProofInitial : IsInitial (mappedProofAlgebra a σ π d Γ hΓ) :=
  Inference.mappedInitial (E) (ifm) (R₁) (canonicalRules a σ π d Γ hΓ)
    (ruleData a σ π d Γ hΓ) (NamedProofImage.proofAlgebra (P) σ π d Γ hΓ)
    (NamedProofImage.proofInitial (P) σ π d Γ hΓ)

def proofAlgebraIso : canonicalProofAlgebra a σ π d Γ hΓ ≅ mappedProofAlgebra a σ π d Γ hΓ :=
  (canonicalProofInitial a σ π d Γ hΓ).uniqueUpToIso (mappedProofInitial a σ π d Γ hΓ)

def proofOverIso : (canonicalProofAlgebra a σ π d Γ hΓ).a ≅
    (Inference.slice (E) (ifm)).functor.obj (NamedProofImage.proofAlgebra (P) σ π d Γ hΓ).a :=
  (Endofunctor.Algebra.forget (canonicalRules a σ π d Γ hΓ).inference).mapIso
    (proofAlgebraIso a σ π d Γ hΓ)

def canonicalProofObject : Total.CanonicalTotal a := (canonicalProofAlgebra a σ π d Γ hΓ).a.left
def canonicalConclusion : canonicalProofObject a σ π d Γ hΓ ⟶ (S₂).algebra.a.2 :=
  (canonicalProofAlgebra a σ π d Γ hΓ).a.hom

def proofIso : canonicalProofObject a σ π d Γ hΓ ≅
    (E).functor.obj (NamedProofImage.proofObject (P) σ π d Γ hΓ) :=
  (Over.forget (S₂).algebra.a.2).mapIso (proofOverIso a σ π d Γ hΓ)

theorem proofIso_conclusion :
    (proofIso a σ π d Γ hΓ).hom ≫
        ((E).functor.map (NamedProofImage.conclusion (P) σ π d Γ hΓ) ≫ (ifm).hom) =
      canonicalConclusion a σ π d Γ hΓ :=
  Over.w (proofOverIso a σ π d Γ hΓ).hom

theorem inverse_proofIso_conclusion :
    (E).functor.map (NamedProofImage.conclusion (P) σ π d Γ hΓ) ≫ (ifm).hom =
      (proofIso a σ π d Γ hΓ).inv ≫ canonicalConclusion a σ π d Γ hΓ := by
  let i := proofIso a σ π d Γ hΓ
  let c := (E).functor.map (NamedProofImage.conclusion (P) σ π d Γ hΓ) ≫ (ifm).hom
  have h := congrArg (fun f : canonicalProofObject a σ π d Γ hΓ ⟶ (S₂).algebra.a.2 => i.inv ≫ f)
    (proofIso_conclusion a σ π d Γ hΓ)
  have hi : i.inv ≫ (i.hom ≫ c)=c := by
    rw [← Category.assoc,i.inv_hom_id,Category.id_comp]
  exact hi.symm.trans h

/-- Constructor preservation is the algebra-isomorphism law; it is proved before passing
to any regular image. -/
theorem proof_constructor :
    (canonicalProofAlgebra a σ π d Γ hΓ).str ≫ (proofOverIso a σ π d Γ hΓ).hom =
      (canonicalRules a σ π d Γ hΓ).inference.map (proofOverIso a σ π d Γ hΓ).hom ≫
        (mappedProofAlgebra a σ π d Γ hΓ).str :=
  (proofAlgebraIso a σ π d Γ hΓ).hom.h.symm

def canonicalSentenceProofObject : Total.CanonicalTotal a :=
  pullback (canonicalConclusion a σ π d Γ hΓ) (S₂).sentenceInclusion

def canonicalSentenceConclusion : canonicalSentenceProofObject a σ π d Γ hΓ ⟶ (S₂).sentenceObject :=
  pullback.snd (canonicalConclusion a σ π d Γ hΓ) (S₂).sentenceInclusion

def mappedSentenceProofIso :
    (E).functor.obj (NamedProofImage.sentenceProofObject (P) σ π d Γ hΓ) ≅
      canonicalSentenceProofObject a σ π d Γ hΓ :=
  pullbackChart (E) (proofIso a σ π d Γ hΓ).symm (mappedSentenceIso a (V) σ π d) (ifm)
    (NamedProofImage.conclusion (P) σ π d Γ hΓ) (S₁).sentenceInclusion
    (canonicalConclusion a σ π d Γ hΓ) (S₂).sentenceInclusion
    (inverse_proofIso_conclusion a σ π d Γ hΓ) (mappedSentenceIso_inclusion a (V) σ π d).symm

def sentenceProofIso : canonicalSentenceProofObject a σ π d Γ hΓ ≅
    (E).functor.obj (NamedProofImage.sentenceProofObject (P) σ π d Γ hΓ) :=
  (mappedSentenceProofIso a σ π d Γ hΓ).symm

theorem sentenceProofIso_conclusion :
    (sentenceProofIso a σ π d Γ hΓ).hom ≫
        (E).functor.map (NamedProofImage.sentenceConclusion (P) σ π d Γ hΓ) =
      canonicalSentenceConclusion a σ π d Γ hΓ ≫ (sentenceIso a (V) σ π d).hom := by
  let m := mappedSentenceProofIso a σ π d Γ hΓ
  let j := mappedSentenceIso a (V) σ π d
  have h := pullbackChart_snd (E) (proofIso a σ π d Γ hΓ).symm j (ifm)
    (NamedProofImage.conclusion (P) σ π d Γ hΓ) (S₁).sentenceInclusion
    (canonicalConclusion a σ π d Γ hΓ) (S₂).sentenceInclusion
    (inverse_proofIso_conclusion a σ π d Γ hΓ) (mappedSentenceIso_inclusion a (V) σ π d).symm
  change (E).functor.map (NamedProofImage.sentenceConclusion (P) σ π d Γ hΓ) ≫ j.hom=
    m.hom ≫ canonicalSentenceConclusion a σ π d Γ hΓ at h
  exact inverse_iso_square m j
    ((E).functor.map (NamedProofImage.sentenceConclusion (P) σ π d Γ hΓ))
    (canonicalSentenceConclusion a σ π d Γ hΓ) h

def mappedSentenceImageInclusion :
    (E).functor.obj (image (NamedProofImage.sentenceConclusion (P) σ π d Γ hΓ)) ⟶ (S₂).sentenceObject :=
  (E).functor.map (image.ι (NamedProofImage.sentenceConclusion (P) σ π d Γ hΓ)) ≫
    (mappedSentenceIso a (V) σ π d).hom

instance mappedSentenceImageInclusion_mono : Mono (mappedSentenceImageInclusion a σ π d Γ hΓ) := by
  dsimp only [mappedSentenceImageInclusion]
  infer_instance

def mappedSentenceImageQuotient : canonicalSentenceProofObject a σ π d Γ hΓ ⟶
    (E).functor.obj (image (NamedProofImage.sentenceConclusion (P) σ π d Γ hΓ)) :=
  (sentenceProofIso a σ π d Γ hΓ).hom ≫
    (E).functor.map (factorThruImage (NamedProofImage.sentenceConclusion (P) σ π d Γ hΓ))

instance mappedSentenceImageQuotient_regularEpi : IsRegularEpi (mappedSentenceImageQuotient a σ π d Γ hΓ) := by
  dsimp only [mappedSentenceImageQuotient]
  infer_instance

theorem mappedSentenceImage_factorization :
    mappedSentenceImageQuotient a σ π d Γ hΓ ≫ mappedSentenceImageInclusion a σ π d Γ hΓ =
      canonicalSentenceConclusion a σ π d Γ hΓ := by
  let c := NamedProofImage.sentenceConclusion (P) σ π d Γ hΓ
  let i := sentenceProofIso a σ π d Γ hΓ
  let j := mappedSentenceIso a (V) σ π d
  have hmap := ((E).functor.map_comp (factorThruImage c) (image.ι c)).symm.trans
    (congrArg (fun f => (E).functor.map f) (image.fac c))
  have hmid := congrArg (fun f => i.hom ≫ f ≫ j.hom) hmap
  have hend := congrArg (fun f : canonicalSentenceProofObject a σ π d Γ hΓ ⟶
      (E).functor.obj (S₁).sentenceObject => f ≫ j.hom)
    (sentenceProofIso_conclusion a σ π d Γ hΓ)
  change (i.hom ≫ (E).functor.map c) ≫ j.hom=
    (canonicalSentenceConclusion a σ π d Γ hΓ ≫ j.inv) ≫ j.hom at hend
  have hid : (canonicalSentenceConclusion a σ π d Γ hΓ ≫ j.inv) ≫ j.hom=
      canonicalSentenceConclusion a σ π d Γ hΓ := by
    rw [Category.assoc,j.inv_hom_id,Category.comp_id]
  change (i.hom ≫ (E).functor.map (factorThruImage c)) ≫
    ((E).functor.map (image.ι c) ≫ j.hom)=_
  have hfinal := hend.trans hid
  simp only [Category.assoc] at hmid hfinal ⊢
  exact hmid.trans hfinal

/-- The canonical generated sentence image is the mapped uniform generated image, in its
sentence coordinates. -/
def sentenceImageIso : image (canonicalSentenceConclusion a σ π d Γ hΓ) ≅
    (E).functor.obj (image (NamedProofImage.sentenceConclusion (P) σ π d Γ hΓ)) :=
  (image.isoStrongEpiMono (mappedSentenceImageQuotient a σ π d Γ hΓ)
    (mappedSentenceImageInclusion a σ π d Γ hΓ)
    (mappedSentenceImage_factorization a σ π d Γ hΓ)).symm

theorem sentenceImageIso_inclusion :
    (sentenceImageIso a σ π d Γ hΓ).hom ≫ mappedSentenceImageInclusion a σ π d Γ hΓ =
      image.ι (canonicalSentenceConclusion a σ π d Γ hΓ) := by
  exact image.isoStrongEpiMono_inv_comp_mono
    (mappedSentenceImageQuotient a σ π d Γ hΓ)
    (mappedSentenceImageInclusion a σ π d Γ hΓ)
    (mappedSentenceImage_factorization a σ π d Γ hΓ)

theorem canonical_sentenceTheory_eq :
    imageSubobject (canonicalSentenceConclusion a σ π d Γ hΓ) =
      Subobject.mk (mappedSentenceImageInclusion a σ π d Γ hΓ) :=
  Subobject.mk_eq_mk_of_comm _ _ (sentenceImageIso a σ π d Γ hΓ)
    (sentenceImageIso_inclusion a σ π d Γ hΓ)

end CategoricalEssentialIncompleteness.V46.Miller.CanonicalPresentation
