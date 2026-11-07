import CategoricalEssentialIncompleteness.V46ArithmeticIndexedFibersAxiomsPredicate
import CategoricalEssentialIncompleteness.V46ArithmeticIndexedFibersNumerals
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.ArithmeticIndexedFibers
open NamedArithmeticSignature
section Generic
universe u₁ u₂ v₁ v₂
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [Regular D] [FinitaryExtensive D]
variable (E : C ≌ D) {A V B S P : C} {W : D}

omit [Regular C] [FinitaryExtensive D] in
private theorem map_terminal (hA : IsTerminal A) (a : E.functor.obj A ≅ ⊤_ D) :
    E.functor.map (hA.from S) = terminal.from (E.functor.obj S) ≫ a.inv := by
  apply (cancel_mono a.hom).mp
  simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]
  exact terminal.hom_ext _ _

/-- A single generic equation carries the terminal, numeral, and product
comparisons before any concrete coded morphism is substituted. -/
private theorem raw_pair_realization (hA : IsTerminal A)
    (a : E.functor.obj A ≅ ⊤_ D) (w : W ≅ E.functor.obj V)
    (f : A ⟶ V) (g : B ⟶ V) (d : TransportedSplitData E a w f g)
    (k : ProductSplitData d.left d.right (E.functor.obj S))
    (p : S ⟶ P) (r : P ⟶ V ⨯ S)
    (hp : p ≫ r = prod.lift (hA.from S ≫ f) (𝟙 S)) :
    E.functor.map p ≫ E.functor.map r ≫ prodComparison E.functor V S ≫
        prod.map w.inv (𝟙 (E.functor.obj S)) = k.left := by
  rw [k.left_primitive]
  apply prod.hom_ext
  · simp only [Category.assoc,prod.map_fst,prodComparison_fst_assoc,prod.lift_fst]
    rw [← Functor.map_comp_assoc,← Functor.map_comp_assoc,hp]
    simp only [prod.lift_fst,Functor.map_comp,Category.assoc]
    rw [map_terminal E hA a,d.left_primitive]
    simp only [Category.assoc]
  · simp only [Category.assoc,prod.map_snd,Category.comp_id,
      prodComparison_snd,prod.lift_snd]
    rw [← Functor.map_comp,← Functor.map_comp,← Category.assoc,hp]
    simp only [prod.lift_snd]
    exact E.functor.map_id S
end Generic

/-- This equality identifies the constructor-preserving numeral leg;
it is not an arbitrary isomorphism between fiber carriers. -/
@[reassoc] theorem realized_rawNumeralPair (e : ℕ) :
    (realization 𝗣𝗔).map (rawNumeralPair ArithmeticIndexedAxioms.sentencePredicate e) ≫
      ArithmeticIndexedAxioms.productIso.hom = fiberMap e ArithmeticIndexedAxioms.sentence := by
  have h := raw_pair_realization (predicateEquivalence 𝗣𝗔)
    (SyntacticPredicates.terminalIsTerminal 𝗣𝗔) realizedTerminalIso
    (ArithmeticOmegaComparison.omegaIso 𝗣𝗔) (numeralPredicate e)
    (complementPredicateInclusion e) (numeralData e)
    (baseData e ArithmeticIndexedAxioms.sentence)
    (rawNumeralPair ArithmeticIndexedAxioms.sentencePredicate e)
    (fromRawProduct 𝗣𝗔 variableSymbols ArithmeticIndexedAxioms.sentencePredicate)
    (rawNumeralPair_product ArithmeticIndexedAxioms.sentencePredicate e)
  simpa only [ArithmeticIndexedAxioms.productIso,ArithmeticIndexedAxioms.rawProductIso,
    Iso.trans_hom,Functor.mapIso_hom,asIso_hom,prod.mapIso_hom,Iso.symm_hom,Iso.refl_hom,
    predicateEquivalence,Functor.asEquivalence_functor,fiberMap] using h

abbrev fiberAxiomObject (AxPA : Carrier) (e : ℕ) : TotalSplit 𝗣𝗔 :=
  (realization 𝗣𝗔).obj (ArithmeticIndexedAxioms.fiberAxioms AxPA e)

def fiberAxioms (AxPA : Carrier) (e : ℕ) :
    fiberAxiomObject AxPA e ⟶ ArithmeticIndexedAxioms.sentence :=
  (realization 𝗣𝗔).map (fiberSentencePredicate AxPA e)

instance fiberAxioms_mono (AxPA : Carrier) (e : ℕ) : Mono (fiberAxioms AxPA e) := by
  unfold fiberAxioms
  infer_instance

def fiberToFamily (AxPA : Carrier) (e : ℕ) :
    fiberAxiomObject AxPA e ⟶ ArithmeticIndexedAxioms.axiomObject AxPA :=
  (realization 𝗣𝗔).map (fiberToFamilyPredicate AxPA e)

/-- The actual numeral fiber of the actual indexed axiom subobject. -/
theorem axiom_pullback (AxPA : Carrier) (e : ℕ) :
    IsPullback (fiberToFamily AxPA e) (fiberAxioms AxPA e)
      (ArithmeticIndexedAxioms.axioms AxPA)
      (fiberMap e ArithmeticIndexedAxioms.sentence) := by
  apply ((predicateAxiom_pullback AxPA e).map (realization 𝗣𝗔)).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) ArithmeticIndexedAxioms.productIso
  · simp [fiberToFamily]
  · simp [fiberAxioms]
  · simp [ArithmeticIndexedAxioms.axioms]
  · simpa only [Iso.refl_hom,Category.id_comp] using realized_rawNumeralPair e

end CategoricalEssentialIncompleteness.V46.ArithmeticIndexedFibers
