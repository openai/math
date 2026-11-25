import OAI.ThreeFlat.RAM.ChunkRequestAddress
import OAI.ThreeFlat.RAM.TickBitRelation

namespace OAI
/-! # Eight physical request words for each auxiliary bit -/

namespace ThreeFlat.RAM.TickBitRelation

open scoped Fin.NatCast

open Computability.VPVNP.BurstRAM ChunkRequests Diagonal.TickAuxiliary

/-- Materializing the eight public-format words per bit prepares the exact
pair of records consumed by the loop. -/
theorem preparedRangeRows_of_words {w a : ℕ} (rules : Fin a → Rule) (m : Memory w)
    (cursor stride : Word w) (pitch : stride.val = 4) (fit : cursor.val + 8*a ≤ 2^w)
    (read : ∀ (i : Fin a) (d : Fin 8), m (cursor.val+8*i.val+d.val) =
      (paddedRequest (rules i) (⟨d.val/4,by omega⟩ : Fin 2) (i.val : Word w)).column
        ⟨d.val%4,Nat.mod_lt _ (by decide)⟩) :
    preparedRows m cursor stride (a*2) = rangeRows rules 0 := by
  apply preparedRows_eq_of_columns m cursor stride (a*2) pitch (by omega)
  intro t col
  obtain ⟨⟨i,s⟩,rfl⟩ := finProdFinEquiv.surjective t
  let d : Fin 8 := ⟨4*s.val+col.val,by have := s.isLt; have := col.isLt; omega⟩
  have hs : (⟨d.val/4,by omega⟩ : Fin 2) = s := by
    apply Fin.ext
    change (4*s.val+col.val)/4 = s.val
    have := col.isLt
    omega
  have hc : (⟨d.val%4,Nat.mod_lt _ (by decide)⟩ : Fin 4) = col := by
    apply Fin.ext
    change (4*s.val+col.val)%4 = col.val
    have := col.isLt
    omega
  have addr : cursor.val+(finProdFinEquiv (i,s)).val*4+col.val = cursor.val+8*i.val+d.val := by
    change cursor.val+(s.val+2*i.val)*4+col.val = cursor.val+8*i.val+(4*s.val+col.val)
    omega
  rw [addr]
  simpa only [hs,hc,rangeRequest,Equiv.symm_apply_apply,Fin.zero_add,Fin.ofNat_eq_cast] using read i d

/-- Natural-address form for a descriptor writing at a fixed start address. -/
theorem preparedRangeRows_nat {w a start : ℕ} (rules : Fin a → Rule) (m : Memory w)
    (fit : start+8*a ≤ 2^w)
    (read : ∀ (i : Fin a) (d : Fin 8), m (start+8*i.val+d.val) =
      (paddedRequest (rules i) (⟨d.val/4,by omega⟩ : Fin 2) (i.val : Word w)).column
        ⟨d.val%4,Nat.mod_lt _ (by decide)⟩) :
    preparedRows m (start : Word w) 4 (a*2) = rangeRows rules 0 := by
  cases a with
  | zero => simp [preparedRows,rangeRows]
  | succ a =>
    have cur : (start : Word w).val = start := Fin.val_cast_of_lt (by omega)
    apply preparedRangeRows_of_words rules m (start : Word w) 4 (Nat.mod_eq_of_lt (show (4:ℕ) < 2^w by omega))
    · rwa [cur]
    · simpa only [cur] using read

end ThreeFlat.RAM.TickBitRelation

end OAI
