import OAI.Computability.VPVNP.CompressorRecordsCursorCoordinates
import OAI.Computability.VPVNP.PairTraversalRows

/-! # Decoding a cursor processor from its initial traversal row -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafCoordinates

open CursorNetwork CursorRouting Compression LocalHistory TraversalRows

variable {b l a p : ℕ} {S : Type} [Fintype S]

/-- The compressor encodes its first binary coordinate at the most
significant bit of the integer. -/
theorem index_bit {n : ℕ} (x : BitWord n) (i : Fin n) :
    (bitWordFinEquiv n x).val.testBit i.val = finTwoEquiv (x i.rev) := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    rw [bitWordFinEquiv_val, Nat.add_comm, Nat.testBit_two_pow_mul_add _ (bitWordFinEquiv n (Fin.tail x)).isLt]
    induction i using Fin.lastCases with
    | last =>
      simp only [Fin.val_last,Nat.lt_irrefl,↓reduceIte,Nat.sub_self,Fin.rev_last]
      generalize x 0 = bit
      fin_cases bit <;> decide
    | cast i =>
      simpa [i.isLt,Fin.rev_castSucc,Fin.tail] using ih (Fin.tail x) i

/-- Undo the order change between the cursor's little-endian address and
the compressor's two big-endian coordinate blocks. -/
theorem site_number (v : Position (b+l)) :
    let u := lanePositions (cursorCoordinateLabels b l) v
    v.2.val = 2^b * (bitWordFinEquiv l u.2).val + (bitWordFinEquiv b u.1.2).val := by
  intro u
  let low := (bitWordFinEquiv b u.1.2).val
  let high := (bitWordFinEquiv l u.2).val
  have hlo : low < 2^b := (bitWordFinEquiv b u.1.2).isLt
  have hhi : high < 2^l := (bitWordFinEquiv l u.2).isLt
  have hsum : 2^b * high + low < 2^(b+l) := calc
    2^b * high + low < 2^b * high + 2^b := Nat.add_lt_add_left hlo _
    _ = 2^b * (high+1) := (Nat.mul_succ ..).symm
    _ ≤ 2^b * 2^l := Nat.mul_le_mul_left _ hhi
    _ = _ := (Nat.pow_add ..).symm
  apply Nat.eq_of_testBit_eq
  intro t
  by_cases h : t < b+l
  · rw [Nat.testBit_two_pow_mul_add _ hlo]
    by_cases ht : t < b
    · let j : Fin b := ⟨t,ht⟩
      rw [ite_eq_left ht]
      change v.2.val.testBit (j.castAdd l).val = (bitWordFinEquiv b u.1.2).val.testBit j.val
      rw [← addressWord_bit, index_bit]
      change finTwoEquiv (addressWord _ v.2 (j.castAdd l)) =
        finTwoEquiv (addressWord _ v.2 (j.rev.rev.castAdd l))
      rw [Fin.rev_rev]
    · let j : Fin l := ⟨t-b,by omega⟩
      have hj : (j.natAdd b).val = t := by change b+(t-b)=t; omega
      rw [ite_eq_right ht, ← hj, ← addressWord_bit v.2 (j.natAdd b), hj]
      change _ = (bitWordFinEquiv l u.2).val.testBit j.val
      rw [index_bit]
      change finTwoEquiv (addressWord _ v.2 (j.natAdd b)) =
        finTwoEquiv (addressWord _ v.2 (j.rev.rev.natAdd b))
      rw [Fin.rev_rev]
  · have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (Nat.le_of_not_gt h)
    exact (Nat.testBit_lt_two_pow (v.2.isLt.trans_le hp)).trans (Nat.testBit_lt_two_pow (hsum.trans_le hp)).symm

theorem leaf_row (hD : 1 < b+l) (hd : 2+p=2^a) (bits : S → ℕ)
    (base cap : ℕ) (v : Position (b+l)) :
    let X := cursorState (cursorCoordinateLabels b l) hD hd bits
    let u := lanePositions (cursorCoordinateLabels b l) v
    let low := (bitWordFinEquiv b u.1.2).val
    let high := (bitWordFinEquiv l u.2).val
    (sitePointers cap base (siteOrder X) u).1 = base + (cap+2)*((v.1.val*2^b+low)*2^l+high) ∧
      v.2.val = 2^b*high + low := by
  intro X u low high
  refine ⟨?_,site_number v⟩
  change base + (cap+2)*(high+2^l*(low+2^b*v.1.val)) = _
  ac_rfl

end PairSimulation.LeafCoordinates

end VPVNP
end Computability
end OAI
