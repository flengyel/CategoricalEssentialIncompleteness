import CategoricalEssentialIncompleteness
import CategoricalEssentialIncompleteness.V46ComparisonChecks
import CategoricalEssentialIncompleteness.V46RegularImageChecks
import CategoricalEssentialIncompleteness.V46SplitExtensionChecks
import CategoricalEssentialIncompleteness.V46ApplicationChecks
import CategoricalEssentialIncompleteness.V46ForkComparisonChecks
import CategoricalEssentialIncompleteness.V46SyntacticChecks
import CategoricalEssentialIncompleteness.V46LogicalChecks
import CategoricalEssentialIncompleteness.V46CategoricalListsChecks
import CategoricalEssentialIncompleteness.V46CategoricalSyntaxChecks
import CategoricalEssentialIncompleteness.V46CategoricalListOperationsChecks
import CategoricalEssentialIncompleteness.V46CategoricalFreeVariablesChecks
import CategoricalEssentialIncompleteness.V46SyntacticSearchChecks
import CategoricalEssentialIncompleteness.V46InferenceChecks
import CategoricalEssentialIncompleteness.V46SentenceImagesChecks
import CategoricalEssentialIncompleteness.V46FirstOrderChecks
import CategoricalEssentialIncompleteness.V46KaroubiChecks

/-! Explicit manuscript types are checked in the imported statement modules.
The consistent-extension statement is also checked independently below. -/

universe v u

open CategoryTheory CategoryTheory.RestrictionCategory
open CategoryTheory.Limits (HasZeroMorphisms)
open CategoricalEssentialIncompleteness.LocalConnectedness

example {C : Type u} [Category.{v} C] [RestrictionCategory C]
    [HasZeroMorphisms C] [RestrictionZero C] [BinaryJoins C] [TotalJoinInverse C]
    {U S : C} {a b : Idem U} (hab : Inseparable a b)
    (θ : U ⟶ S) (hθ : isTotal θ) (ν : S ⟶ S) (hν : isTotal ν)
    (t₀ : Idem S) (ha : a ≤ Idem.pull θ t₀)
    (hb : b ≤ Idem.pull θ (Idem.pull ν t₀))
    (t : Idem S) (ht : t₀ ≤ t) (hc : t ⊓ Idem.pull ν t = ⊥) :
    Inseparable t (Idem.pull ν t) ∧ t ⊔ Idem.pull ν t ≠ ⊤ :=
  domain_incompleteness hab θ hθ ν hν t₀ ha hb t ht hc
