import CategoricalEssentialIncompleteness.V46MillerUniformFinite
namespace CategoricalEssentialIncompleteness.V46.Miller.Uniform.Checks
example {P : Family} {α : Type} [Primcodable α] {R : α → Prop} (hR : Enumerable P R) :
    Enumerable P (fun L : List α => ∀ x ∈ L,R x) := hR.listAll
example {P : Family} {α β : Type} [Primcodable α] [Primcodable β]
    {R : α → Prop} (hR : Enumerable P R) (L : β → List α) (hL : Computable L) :
    Enumerable P (fun b => ∀ x ∈ L b,R x) := hR.finiteRecord L hL
end CategoricalEssentialIncompleteness.V46.Miller.Uniform.Checks
