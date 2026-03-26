module

public import Mathlib.Data.Vector.Basic

@[expose] public section


abbrev Similarity := Nat → Type*

inductive Formula (τ : Similarity) (α : Type*)
| atom   : α → Formula τ α
| falsum : Formula τ α
| imply  : Formula τ α → Formula τ α → Formula τ α
| dia'   : {arity : Nat} → τ arity → (Fin arity → Formula τ α) → Formula τ α

variable {τ : Similarity} {α : Type*}

abbrev FormulaSeq (τ α arity) := Vector (Formula τ α) arity

namespace Formula


prefix:75 "#" => atom
infixr:67 " 🡒 " => imply

abbrev dia {arity : Nat} (t : τ arity) (Φ : FormulaSeq τ α arity) : Formula τ α := dia' t Φ.get
notation:91 "△[" t "]" Φ => dia t Φ

notation:max "⊥" => falsum

abbrev neg (φ : Formula τ α) : Formula τ α := φ 🡒 ⊥
prefix:85 "∼" => neg

abbrev or (φ ψ : Formula τ α) : Formula τ α := ∼φ 🡒 ψ
infixr:68 " ⋎ " => or

abbrev and (φ ψ : Formula τ α) : Formula τ α := ∼(φ 🡒 ∼ψ)
infixr:69 " ⋏ " => and

abbrev verum : Formula τ α := ∼⊥
notation:max "⊤" => ∼⊥

abbrev iff (φ ψ : Formula τ α) : Formula τ α := (φ 🡒 ψ) ⋏ (ψ 🡒 φ)
notation:70 " 🡘 " => iff

end Formula


namespace FormulaSeq

abbrev neg (Φ : FormulaSeq τ α arity) : FormulaSeq τ α arity := Φ.map Formula.neg
prefix:85 "∼" => neg

variable {Φ : FormulaSeq τ α arity} {i : Fin arity}

@[grind =] lemma eq_neg_get_get_neg : (∼Φ).get i = ∼(Φ.get i) := by apply Vector.getElem_map

end FormulaSeq


namespace Formula

abbrev box {arity : ℕ} (t : τ arity) (Φ : FormulaSeq τ α arity) : Formula τ α := ∼(△[t](∼Φ))
notation:91 "▽[" t "]" Φ => box t Φ

end Formula

end
