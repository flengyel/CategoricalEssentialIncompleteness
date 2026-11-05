import CategoricalEssentialIncompleteness.V46NamedFiniteSoundness

universe u v w
namespace CategoricalEssentialIncompleteness.V46.NamedFiniteSoundnessChecks
open NamedFiniteSyntax
variable {Sig : ℕ → Type u} {Rel : ℕ → Type v} {d : ℕ} {K : Type w}
variable (functions : ∀ n : Fin (d + 1), Sig n.val → (Fin n.val → K) → K)
  (relations : ∀ n : Fin (d + 1), Rel n.val → (Fin n.val → K) → Prop)
example (φ ψ : Formula Sig Rel d) :
    Formula.Valid functions relations (.imp φ (.imp ψ φ)) :=
  Formula.valid_one functions relations φ ψ
example (φ ψ χ : Formula Sig Rel d) :
    Formula.Valid functions relations
      (.imp (.imp φ (.imp ψ χ)) (.imp (.imp φ ψ) (.imp φ χ))) :=
  Formula.valid_two functions relations φ ψ χ
example (φ ψ : Formula Sig Rel d) :
    Formula.Valid functions relations (.imp (.imp (.neg ψ) (.neg φ)) (.imp φ ψ)) :=
  Formula.valid_three functions relations φ ψ
example (φ ψ : Formula Sig Rel d) (x : ℕ) (t : Term Sig d)
    (h : φ.substitute x t = some ψ) :
    Formula.Valid functions relations (.imp (.all x φ) ψ) :=
  Formula.valid_instantiation functions relations φ ψ x t h
example (φ ψ : Formula Sig Rel d) (x : ℕ) (hx : x ∉ φ.freeVariables) :
    Formula.Valid functions relations (.imp (.all x (.imp φ ψ)) (.imp φ (.all x ψ))) :=
  Formula.valid_distribution functions relations φ ψ x hx
example (t : Term Sig d) : Formula.Valid functions relations (.equal t t) :=
  Formula.valid_reflexivity functions relations t
example (φ φu φt : Formula Sig Rel d) (u t : Term Sig d) (x : ℕ)
    (hu : φ.substitute x u = some φu) (ht : φ.substitute x t = some φt) :
    Formula.Valid functions relations (.imp (.equal u t) (.imp φu φt)) :=
  Formula.valid_equality functions relations φ φu φt u t x hu ht
example (φ ψ : Formula Sig Rel d)
    (hi : Formula.Valid functions relations (.imp φ ψ))
    (hf : Formula.Valid functions relations φ) : Formula.Valid functions relations ψ :=
  Formula.valid_modusPonens functions relations φ ψ hi hf
example (φ : Formula Sig Rel d) (x : ℕ) (h : Formula.Valid functions relations φ) :
    Formula.Valid functions relations (.all x φ) :=
  Formula.valid_generalization functions relations φ x h
example [Nonempty K] (φ : Formula Sig Rel d) (h : Formula.Valid functions relations φ)
    (hn : Formula.Valid functions relations (.neg φ)) : False :=
  Formula.valid_negation_disjoint functions relations φ h hn
end CategoricalEssentialIncompleteness.V46.NamedFiniteSoundnessChecks
