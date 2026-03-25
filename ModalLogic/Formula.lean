module

import Mathlib.Data.Vector.Basic

@[expose] public section


abbrev Similarity := Nat → Type*

inductive Formula (τ : Similarity) (α : Type*)
| atom   : α → Formula τ α
| falsum : Formula τ α
| imply  : Formula τ α → Formula τ α → Formula τ α
| dia    : {arity : Nat} → τ arity → (Fin arity → Formula τ α) → Formula τ α

variable {τ : Similarity} {α : Type*}

namespace Formula

prefix:75 "#" => atom
infixr:67 " → " => imply
notation:91 "▽[" t "]" Φ => dia t Φ
notation:max "⊥" => falsum

abbrev neg (φ : Formula τ α) : Formula τ α := φ → ⊥
prefix:85 "∼" => neg

abbrev or (φ ψ : Formula τ α) : Formula τ α := ∼φ → ψ
infixr:68 " ⋎ " => or

abbrev and (φ ψ : Formula τ α) : Formula τ α := ∼(φ → ∼ψ)
infixr:69 " ⋏ " => and

abbrev verum : Formula τ α := ∼⊥
notation:max "⊤" => ∼⊥

end Formula


abbrev FormulaSeq (ar : ℕ) (τ) (α) := Fin ar → Formula τ α
namespace FormulaSeq

abbrev neg (Φ : FormulaSeq ar τ α) : FormulaSeq ar τ α := λ i => ∼(Φ i)
prefix:85 "∼" => neg

end FormulaSeq


namespace Formula

abbrev box {arity : ℕ} (t : τ arity) (Φ : FormulaSeq arity τ α) : Formula τ α := ∼(▽[t](∼Φ))
notation:91 "△[" t "]" Φ => box t Φ

end Formula

end
