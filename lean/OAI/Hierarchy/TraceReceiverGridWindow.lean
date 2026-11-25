import OAI.Hierarchy.GridReceiverBankAddresses

namespace OAI
/-! # Address separation of the native receiver's terminal workspace -/
namespace Hierarchy.TraceFactorReceiver.Gather
open ThreeFlat Diagonal
variable {w u : ℕ}

/-- All receiver workspace words through S44 lie below sector 30. Its command
and map arrays use a fixed sixteen gaps of size 2^(4w). -/
theorem grid_window (large : 7≤w) (age : u^10≤5*w) :
    TickWorkspace.base u 45 < GridReceiverBanks.base w ∧
      GridReceiverBanks.base w+16*GridReceiverBanks.gap w<2^(64*w) ∧
      128≤GridReceiverBanks.gap w := by
  let B:=GridDescription.sector w
  let S:=GridReceiverBanks.gap w
  have exp : TickWorkspace.stride u=2^(u^10*4) := (pow_mul ..).symm
  have first : TickWorkspace.base u 45<B := calc
    _ ≤ 2^6*TickWorkspace.stride u := Nat.mul_le_mul_right _ (by decide)
    _ = 2^(6+u^10*4) := by rw [exp,pow_add]
    _ < B := Nat.pow_lt_pow_right (by decide) (by omega : 6+u^10*4<32*w)
  have gap : S≤B := Nat.pow_le_pow_right (by decide) (by omega : 4*w≤32*w)
  have roof : 2^6*B<2^(64*w) := by
    change 2^6*2^(32*w)<_
    rw [←pow_add]
    exact Nat.pow_lt_pow_right (by decide) (by omega)
  have pages : 128≤S := Nat.pow_le_pow_right (by decide : 0<2) (by omega : 7≤4*w)
  change TickWorkspace.base u 45<30*B ∧ 30*B+16*S<2^(64*w) ∧ 128≤S
  norm_num at roof
  omega

end Hierarchy.TraceFactorReceiver.Gather

end OAI
