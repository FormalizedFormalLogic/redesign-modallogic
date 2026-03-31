module

public import Mathlib.Data.Vector.Basic

@[expose] public section


def Vector.mkFn {α : Type*} {n : ℕ} (f : Fin n → α) : Vector α n := ⟨Array.ofFn f, by simp⟩


abbrev Similarity := Nat → Type*

inductive Formula (τ : Similarity) (α : Type*)
| atom   : α → Formula τ α
| falsum : Formula τ α
| imply  : Formula τ α → Formula τ α → Formula τ α
| dia   : {arity : Nat} → τ arity → (Fin arity → Formula τ α) → Formula τ α

variable {τ : Similarity} {α : Type*}

abbrev FormulaSeq (τ α arity) := Fin arity → Formula τ α

namespace Formula


prefix:75 "#" => atom
infixr:67 " 🡒 " => imply

-- abbrev dia {arity : Nat} (t : τ arity) (Φ : FormulaSeq τ α arity) : Formula τ α := dia' t Φ.get
notation:91 "△[" t "]" Φ => dia t Φ

/-
lemma eq_dia'_dia {arity t} {Φ : Fin arity → Formula τ α} : dia' t Φ = dia t (Vector.mkFn Φ) := by
    simp only [dia, Vector.mkFn, dia'.injEq, heq_eq_eq, true_and];
    ext i;
    simp [Vector.get]
-/

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

abbrev neg (Φ : FormulaSeq τ α arity) : FormulaSeq τ α arity := λ i => ∼(Φ i)
prefix:85 "∼" => neg

variable {Φ : FormulaSeq τ α arity} {i : Fin arity}

-- @[grind =] lemma eq_neg_get_get_neg : (∼Φ).get i = ∼(Φ.get i) := by apply Vector.getElem_map

end FormulaSeq


namespace Formula

abbrev box {arity : ℕ} (t : τ arity) (Φ : FormulaSeq τ α arity) : Formula τ α := ∼(△[t](∼Φ))
notation:91 "▽[" t "]" Φ => box t Φ


@[grind]
def length : Formula τ α → Nat
    | .atom _    => 1
    | .falsum    => 1
    | .imply φ ψ => 1 + φ.length + ψ.length
    | .dia _ Φ  => 1 + (List.ofFn (λ i => (Φ i).length)).sum

@[simp, grind .]
lemma length_pos {φ : Formula τ α} : φ.length > 0 := by induction φ <;> grind;

lemma length_lt_imply₁ : φ.length < (φ 🡒 ψ).length := by grind;
lemma length_lt_imply₂ : ψ.length < (φ 🡒 ψ).length := by grind;
lemma length_lt_dia : (Φ i).length < (△[t]Φ).length := by
    dsimp [length];
    sorry;

/-
@[elab_as_elim]
def cases' {C : Formula τ α → Sort w}
  (falsum : C ⊥)
  (atom   : ∀ a : α, C (atom a))
  (imply  : ∀ (φ ψ : Formula τ α), C (φ 🡒 ψ))
  (dia    : ∀ {arity : ℕ}, ∀ (t : τ arity) (Φ : FormulaSeq τ α arity), C (△[t]Φ))
    : (φ : Formula τ α) → C φ
    | ⊥            => falsum
    | .atom a      => atom a
    | .imply φ ψ   => imply φ ψ
    | .dia' t Φ    => by rw [eq_dia'_dia]; apply dia;

@[induction_eliminator]
def rec' {C : Formula τ α → Sort w}
  (falsum : C ⊥)
  (atom   : ∀ a : α, C (atom a))
  (imply  : ∀ (φ ψ : Formula τ α), C φ → C ψ → C (φ 🡒 ψ))
  (dia    : ∀ {arity}, ∀ (t : τ arity) (Φ : FormulaSeq τ α arity), (∀ i, C (Φ.get i)) → C (△[t]Φ))
  : (φ : Formula τ α) → C φ
  | ⊥      => falsum
  | #a     => atom a
  | φ 🡒 ψ  =>
    have : φ.length < (φ 🡒 ψ).length := length_lt_imply₁;
    have : ψ.length < (φ 🡒 ψ).length := length_lt_imply₂;
    imply φ ψ (rec' falsum atom imply dia φ) (rec' falsum atom imply dia ψ)
  | .dia' t Φ => by
    rw [eq_dia'_dia];
    apply dia;
    intro i;
    sorry;
    -- have := length_lt_dia' (i := i) (t := t) (Φ := Φ);
    -- apply rec' falsum atom imply dia;
termination_by φ => φ.length
-/

end Formula



end
