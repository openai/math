import OAI.ThreeFlat.RAM.TickIdentity
import OAI.ThreeFlat.RAM.TickBitRelation

namespace OAI
/-! # Preserving external chunk bits in nonscan history phases -/

namespace ThreeFlat.RAM.TickChunkPreserve

open Computability.VPVNP.BurstRAM PrivateRAM ContinuationLink
open scoped Classical

variable {w p r k a : ℕ} {F : Type*} [Semiring F]

/-- The nonscan phase reads the two physical chunk arrays directly. -/
abbrev block (w left right a : ℕ) := TickIdentity.compare w left right a

theorem agree_iff (m : Memory w) (left right : ℕ) (old new : Fin a → Bool)
    (width : 1 < 2^w)
    (readOld : ∀ i : Fin a, m (left+i.val) = TickBitRelation.bitWord w (old i))
    (readNew : ∀ i : Fin a, m (right+i.val) = TickBitRelation.bitWord w (new i)) :
    ScanLoop.agree m left right a ↔ old = new := by
  have z : (0 : Word w).val = 0 := rfl
  have o : (1 : Word w).val = 1 := Nat.mod_eq_of_lt width
  have nz : (1 : Word w) ≠ 0 := fun h => by have := congrArg Fin.val h; omega
  have inj : Function.Injective (TickBitRelation.bitWord w) := by
    intro x y h
    cases x <;> cases y
    · rfl
    · exact (nz h.symm).elim
    · exact (nz h).elim
    · rfl
  simp only [ScanLoop.agree,readOld,readNew,inj.eq_iff,funext_iff]

/-- The pass uses seven registers, fourteen rows, and a caller-supplied
continuation. The external memory is preserved, including all history data. -/
theorem mass_block (field : FieldCode F w) (M : Machine w p r k) (left right : ℕ)
    (pc : Fin 14 ↪ Fin p) (reg : Fin 7 ↪ Fin r) (pub : Fin 0 → Fin k) (exit : Fin p)
    (rom : (block w left right a).Installed M pc reg pub exit) (c : Config w p r) (m : Memory w)
    (entry : c.pc = pc (block w left right a).first)
    (fitL : left+a < 2^w) (fitR : right+a < 2^w)
    (old new : Fin a → Bool) (width : 1 < 2^w)
    (readOld : ∀ i : Fin a, m (left+i.val) = TickBitRelation.bitWord w (old i))
    (readNew : ∀ i : Fin a, m (right+i.val) = TickBitRelation.bitWord w (new i)) :
    ∃ d : Config w p r, d.pc = exit ∧ ∀ fuel, mass field M.program (fuel+8+6*a) c m =
      if old = new then mass field M.program fuel d m else 0 := by
  simpa only [agree_iff m left right old new width readOld readNew] using
    TickIdentity.mass_compare field M left right a pc reg pub exit rom c m entry fitL fitR


end ThreeFlat.RAM.TickChunkPreserve

end OAI
