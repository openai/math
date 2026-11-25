import OAI.ThreeFlat.RAM.ChunkRequestContinue
import OAI.ThreeFlat.RAM.ChunkRequestReplay
import OAI.ThreeFlat.RAM.TickBitAddress

namespace OAI
/-! # Continuing from a verified auxiliary bit range -/

namespace ThreeFlat.RAM.TickBitRelation

open scoped Fin.NatCast

open Computability.VPVNP.BurstRAM PrivateRAM ChunkRequests Diagonal.TickAuxiliary
open scoped Classical

/-- The relation check transfers successful native control to the caller's
selected continuation, with the same endpoint history and external memory. -/
theorem mass_range_continue {w p r k n : ℕ} {F : Type*} [Semiring F] (field : FieldCode F w)
    (M : Machine w p r k) (R : Registers w k r) (L : Labels w k p)
    (zeroReg : Fin r) (test bad next : Fin p)
    (rom : ContinueInstalled M R L zeroReg test bad next) (rules : Fin n → Rule) (fuel : ℕ)
    (c : Config w p r) (m : Memory w) (a b : Fin n → Bool) (width : 2 < 2^w)
    (pc : c.pc = L.guard) (stride : (c.reg (R.slot 5)).val = 4)
    (size : (c.reg (R.slot 0)).val + (n*2)*4 = (c.reg (R.slot 6)).val)
    (tag : c.reg (R.slot 1) = 0) (flag : c.reg (R.slot 4) ≠ 0)
    (read : ∀ (i : Fin n) (d : Fin 8), m ((c.reg (R.slot 0)).val+8*i.val+d.val) =
      (paddedRequest (rules i) (⟨d.val/4,by omega⟩ : Fin 2) (i.val : Word w)).column
        ⟨d.val%4,Nat.mod_lt _ (by decide)⟩)
    (old_ok : ∀ j : Fin n, bitAt m (c.reg (R.slot 2)) (j.val : Word w) = bitWord w (a j))
    (new_ok : ∀ j : Fin n, bitAt m (c.reg (R.slot 3)) (j.val : Word w) = bitWord w (b j)) :
    let out := scan M.publicData R L (n*2) c m
    mass field M.program (fuel+3+n*122) c m =
      if ∀ j, (rules j).holds (a j) (b j) then
        mass field M.program fuel (out.1.put next zeroReg 0) m else 0 := by
  dsimp only
  rw [show n*122 = (n*2)*61 by omega,
    mass_continue field M R L zeroReg test bad next rom _ fuel c m pc stride size flag]
  apply ite_congr _ (fun _ => rfl) (fun _ => rfl)
  apply propext
  have fit : (c.reg (R.slot 0)).val+8*n ≤ 2^w := by
    have := (c.reg (R.slot 6)).isLt
    omega
  rw [allRows_prepared, preparedRangeRows_of_words rules m _ _ stride fit read, tag]
  apply rangeRows_matches width rules m _ _ 0 a b
  · simpa only [Fin.zero_add,Fin.ofNat_eq_cast] using old_ok
  · simpa only [Fin.zero_add,Fin.ofNat_eq_cast] using new_ok


end ThreeFlat.RAM.TickBitRelation

end OAI
