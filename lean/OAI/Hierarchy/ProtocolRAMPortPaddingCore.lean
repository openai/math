import Mathlib.Data.Fin.Basic

namespace OAI
/-! # Extending finite tables at a larger port count -/

namespace Hierarchy.ProtocolRAM.PortPadding
variable {n D : ℕ}

/-- A real role keeps its ordinal in the larger universal occurrence board. -/
def inject (bound : n ≤ D) (i : Fin n) : Fin D := ⟨i.val,Nat.lt_of_lt_of_le i.isLt bound⟩

def extend {α : Type*} (source : Fin n → α) (dead : α) (i : Fin D) : α :=
  if hi : i.val < n then source ⟨i.val,hi⟩ else dead

@[simp] theorem extend_real {α : Type*} (f : Fin n → α) (v : α) (bound : n ≤ D) (i : Fin n) :
    extend f v (inject bound i) = f i := by simp [extend,inject,i.isLt]

theorem extend_tail {α : Type*} (f : Fin n → α) (v : α) (i : Fin D) (hi : n ≤ i.val) :
    extend f v i = v := by simp [extend,Nat.not_lt.mpr hi]

end Hierarchy.ProtocolRAM.PortPadding

end OAI
