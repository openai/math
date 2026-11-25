import OAI.Computability.VPVNP.PrimedStackRAMCode

namespace OAI
/-! # Embedding ordered native operations at given program counters -/

namespace ThreeFlat.RAM.NativeRows

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.PrimedStackRAM

variable {w p r k : ℕ}

/-- Every operation has its own native row and proceeds to the next position.
The last position may be the first row of another block. -/
def opRows (w : ℕ) (xs : List (Op r k)) (loc : Fin (xs.length+1) → Fin p)
    (bad : Fin p) (i : Fin xs.length) : Instr w p r k :=
  ((xs.get i).emit (loc i.succ) bad).resize w

theorem contains_opRows (M : Machine w p r k) (bad : Fin p) (xs : List (Op r k))
    (loc : Fin (xs.length+1) → Fin p)
    (rows : ∀ i : Fin xs.length, M.code (loc i.castSucc) = opRows w xs loc bad i) :
    Contains M bad (loc 0) xs (loc (Fin.last xs.length)) := by
  induction xs with
  | nil => exact .nil _
  | cons x xs ih =>
    apply Contains.cons (next := loc (⟨0,by simp⟩ : Fin (x::xs).length).succ) (rows ⟨0,by simp⟩)
    exact ih (fun i => loc i.succ) (fun i => rows i.succ)

end ThreeFlat.RAM.NativeRows

end OAI
