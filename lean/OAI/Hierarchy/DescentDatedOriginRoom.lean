import OAI.Hierarchy.DescentDonorWidths
import OAI.Hierarchy.DescentSignedCableFields

namespace OAI
/-! # The ordinary origin and eleven-role ticket fit the purchased donor lookup -/
namespace Hierarchy.DescentRawCablePanel.DepotRAM
open DescentSharedCableNames DescentSIMDLookup
noncomputable section

/-- The same small numeric key width fits both the old local name and the
dynamically selected original outgoing/role ticket. -/
def originBits (s : Shape) := DescentSignedCableCodec.width s.degree s.cap+4

private theorem alphabet (n : ℕ) : n<2^Packed.bits n :=
  (Nat.lt_succ_self n).trans_le (Nat.le_pow_clog (by decide) (n+1))

theorem origin_name_fits (s : Shape) (peer : Fin s.degree) (first : Fin s.cap) :
    1+peer.val*s.cap+first.val<2^originBits s := by
  have len : 1+peer.val*s.cap+first.val≤ s.degree*s.cap := by
    calc
      _ ≤ (peer.val+1)*s.cap := by rw [Nat.add_mul,Nat.one_mul];have:=first.isLt;omega
      _ ≤ s.degree*s.cap := Nat.mul_le_mul_right _ peer.isLt
  have large : s.degree*s.cap < 2^Packed.bits s.degree*2^Packed.bits s.cap :=
    (Nat.mul_lt_mul_of_pos_right (alphabet s.degree) (Nat.zero_lt_of_lt first.isLt)).trans_le
      (Nat.mul_le_mul_left _ (alphabet s.cap).le)
  have width : Packed.bits s.degree+Packed.bits s.cap≤ originBits s :=by
    unfold originBits DescentSignedCableCodec.width;omega
  exact len.trans_lt (large.trans_le (by rw [←pow_add];exact Nat.pow_le_pow_right (by decide) width))

theorem origin_role_fits (s : Shape) (old : Fin s.cap) (role : Fin 11) :
    1+11*old.val+role.val<2^originBits s := by
  have one:=old.isLt
  have two:=role.isLt
  have bits : Packed.bits s.cap≤ DescentSignedCableCodec.width s.degree s.cap :=by
    unfold DescentSignedCableCodec.width;omega
  have high:=(alphabet s.cap).trans_le (Nat.pow_le_pow_right (by decide : 0<2) bits)
  rw [originBits,pow_add]
  norm_num
  omega

theorem originBits_le (s : Shape) (cells : 0<s.blocks) (ports : 0<s.cap) :
    originBits s≤ totalBits s := by
  let b:=DescentSignedCableCodec.width s.degree s.cap
  have capBit : 0<Packed.bits s.cap :=by
    have:=alphabet s.cap
    by_contra! z
    rw [Nat.eq_zero_of_le_zero z] at this
    omega
  have size : 4≤ b :=by dsimp [b,DescentSignedCableCodec.width];omega
  have seats : 2≤ s.blocks*(2*s.cap) :=by
    calc 2=1*(2*1):=by decide
         _≤ s.blocks*(2*s.cap):=Nat.mul_le_mul cells (Nat.mul_le_mul_left 2 ports)
  have cable : b*2≤ cableBits s:=Nat.mul_le_mul_left _ seats
  change b+4≤_
  unfold totalBits
  omega

theorem origin_lookup_paid (s : Shape) (cells : 0<s.blocks) (ports : 0<s.cap)
    (unit M w : ℕ) (funded : 2*totalBits s+1≤ unit) (payload : M*unit≤ w/2) :
    totalBits s+originBits s≤ unit ∧ (totalBits s+originBits s)*M≤ w/2 := by
  have small:=originBits_le s cells ports
  have combined : totalBits s+originBits s≤ unit:=by omega
  exact ⟨combined,(Nat.mul_le_mul_right M combined).trans (by simpa [Nat.mul_comm] using payload)⟩

end
end Hierarchy.DescentRawCablePanel.DepotRAM

end OAI
