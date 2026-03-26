module

public import ModalLogic.Formula

@[expose] public section

variable {τ : Similarity} {α : Type*}
variable {a : α} {φ ψ : Formula τ α}

structure KripkeFrame (τ : Similarity) (κ : Type*) where
  Rel' : {arity : ℕ} → τ arity → κ → Vector κ arity → Prop

namespace KripkeFrame

variable {F : KripkeFrame τ κ}

abbrev World (_ : KripkeFrame τ κ) := κ
abbrev Rel {arity : ℕ} (t : τ arity) (w : F.World) (v : Vector F.World arity) : Prop := F.Rel' t w v
notation:91 w " ≺[" t "] " v => Rel t w v

end KripkeFrame

structure KripkeModel (τ : Similarity) (α : Type*) (κ : Type*) extends KripkeFrame τ κ where
  val : κ → α → Prop


namespace Formula

variable {M : KripkeModel τ α κ} {w : M.World}
variable {arity} {t : τ arity} {Φ : FormulaSeq τ α arity}

@[grind]
def KripkeForced {M : KripkeModel τ α κ} (w : M.World) : Formula τ α → Prop
| .atom a => M.val w a
| .falsum => False
| .imply φ ψ => KripkeForced w φ → KripkeForced w ψ
| .dia' t Φ => ∃ v, (w ≺[t] v) ∧ ∀ i, KripkeForced v[i] (Φ i)
infixr:25 " ⊩ " => KripkeForced

abbrev NotKripkeForced (w : M.World) (φ : Formula τ α) : Prop := ¬(w ⊩ φ)
infixr:25 " ⊮ " => NotKripkeForced

lemma kripkeForced_atom   : w ⊩ #a ↔ M.val w a := by rfl
lemma kripkeForced_falsum : w ⊮ ⊥ := by grind
lemma kripkeForced_imply  : w ⊩ φ 🡒 ψ ↔ (w ⊩ φ) → (w ⊩ ψ) := by rfl
lemma kripkeForced_dia    : w ⊩ (△[t]Φ) ↔ ∃ v, (w ≺[t] v) ∧ ∀ i, (v[i]) ⊩ (Φ.get i) := by rfl
lemma kripkeForced_and    : w ⊩ φ ⋏ ψ ↔ (w ⊩ φ) ∧ (w ⊩ ψ) := by grind
lemma kripkeForced_or     : w ⊩ φ ⋎ ψ ↔ (w ⊩ φ) ∨ (w ⊩ ψ) := by grind
lemma kripkeForced_neg    : w ⊩ ∼φ ↔ w ⊮ φ := by grind
lemma kripkeForced_verum  : w ⊩ ⊤ := by grind
lemma kripkeForced_box    : w ⊩ (▽[t]Φ) ↔ ∀ v, (w ≺[t] v) → ∃ i, (v[i]) ⊩ (Φ.get i) := by
    rw [kripkeForced_neg, NotKripkeForced, kripkeForced_dia];
    grind;

attribute [grind =_]
    kripkeForced_and
    kripkeForced_or
    kripkeForced_neg

attribute [grind .]
    kripkeForced_verum
    kripkeForced_falsum

def KripkeModelValid (M : KripkeModel τ α κ) (φ : Formula τ α) : Prop := ∀ w : M.World, w ⊩ φ
infix:25 " ⊧ " => KripkeModelValid

def KripkeFrameValid (F : KripkeFrame τ κ) (φ : Formula τ α) : Prop := ∀ V, (⟨F, V⟩ : KripkeModel τ α κ) ⊧ φ
infix:25 " ⊧ " => KripkeFrameValid

end Formula

end
