import OAI.ThreeFlat.Diagonal.AlignedChunks
import OAI.ThreeFlat.Diagonal.TickChronology

namespace OAI
/-! # The alternating half and low chunk of the native chronological clock -/

namespace ThreeFlat.Diagonal.AlignedChunks

open TickChronology
variable {period width : ℕ}

def order (c : Clock) (size : c.chunks=2*(period*width)) : Fin c.chunks ≃ Bool × Fin (period*width) :=
  (finCongr size).trans (finProdFinEquiv.symm.trans (finTwoEquiv.prodCongr (Equiv.refl _)))

private theorem side_val (b : ℕ) :
    (finTwoEquiv.symm (b.testBit 0)).val = b%2 := by
  rcases Nat.mod_two_eq_zero_or_one b with h|h <;> simp [h,finTwoEquiv]

theorem visited (c : Clock) (size : c.chunks=2*(period*width)) [NeZero period]
    (b : ℕ) (j : Fin width) :
    (active period b,slot (phase period b) j) =
      order c size ⟨(b*width+j.val)%c.chunks,Nat.mod_lt _ c.chunks_pos⟩ := by
  apply (order c size).symm.injective
  rw [Equiv.symm_apply_apply]
  apply Fin.ext
  change (slot (phase period b) j).val+(period*width)*(finTwoEquiv.symm (active period b)).val = _
  rw [slot_nat,active,side_val]
  change b%period*width+j.val+period*width*(b/period%2) = (b*width+j.val)%c.chunks
  rw [size]
  let u := b%period*width+j.val + period*width*(b/period%2)
  have hp := Nat.pos_of_ne_zero (NeZero.ne period)
  have low : b%period*width+j.val < period*width := by
    have d := Nat.mul_le_mul_right width (Nat.mod_lt b hp)
    have e := j.isLt
    rw [Nat.succ_mul] at d
    omega
  have side : b/period%2 ≤ 1 := by have := Nat.mod_lt (b/period) (by decide : 0<2); omega
  have uBound : u < 2*(period*width) := by
    have le := Nat.mul_le_mul_left (period*width) side
    dsimp [u]
    omega
  have whole : b*width+j.val = u + (2*(period*width))*(b/period/2) := by
    calc b*width+j.val =
        (b%period+(b/period%2+2*(b/period/2))*period)*width+j.val := by
          rw [Nat.mod_add_div (b/period) 2,Nat.mod_add_div']
      _ = _ := by dsimp [u]; ring
  rw [whole,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt uBound]

end ThreeFlat.Diagonal.AlignedChunks

end OAI
