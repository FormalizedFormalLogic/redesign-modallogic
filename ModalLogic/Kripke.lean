module

public import ModalLogic.Formula

@[expose] public section

variable {α : Type u}

structure KripkeFrame (κ : Type*) where
  acc : κ → κ → Prop

end
