import OAI.Hierarchy.DescentResetSenderFieldWidth

namespace OAI
/-! # Bounds on the finite sender selectors at the actual root-field width -/
namespace Hierarchy.DescentDatedAddressBook.ResetMiddle
open DescentResetLocalRoster DescentDenseHostOrder
noncomputable section
variable (D cap n k Ht : ℕ)
local notation "field" => fieldWidth D cap n k Ht

structure PacketSenderLimits : Prop where
  precision : 2*k+n+2≤field
  depthFit : k+1<2^field
  capFit : cap<2^field
  baseRoom : max (max k (2^n)) (2^k)<2^field
  dimension : n<field
  socketRoom : rootSlots k (2^n)*(2^n+2^Ht)<2^field
  heightRoom : Ht<2^field
  portRoom : D≤2^field
  rankRoom : Ht+2≤field
  rankStrict : Ht+2<field

theorem packet_sender_limits : PacketSenderLimits D cap n k Ht :=by
  have size:=sender_field D cap n k Ht
  unfold senderWidth at size
  have logD : Nat.clog 2 (D+1)≤field:=by
    have e : DescentSignedCableCodec.width D cap≤DescentFallbackPeriod.packetField D cap n k Ht:=
      (le_max_left ..).trans (le_max_right ..)
    exact (show Nat.clog 2 (D+1)≤DescentSignedCableCodec.width D cap by
      unfold DescentSignedCableCodec.width DescentSharedCableNames.Packed.bits
      omega).trans (e.trans (le_max_left ..))
  have exp : field<2^field:=Nat.lt_two_pow_self
  have capExp : cap+1≤2^field:=(Nat.le_pow_clog (by decide : 1<2) _).trans
    (Nat.pow_le_pow_right (by decide) (show Nat.clog 2 (cap+1)≤field by omega))
  have dExp : D+1≤2^field:=(Nat.le_pow_clog (by decide : 1<2) _).trans (Nat.pow_le_pow_right (by decide) logD)
  have nsmall : n<field:=by omega
  have ksmall : k<field:=by omega
  have en : 2^n<2^field:=Nat.pow_lt_pow_right (by decide) nsmall
  have ek : 2^k<2^field:=Nat.pow_lt_pow_right (by decide) ksmall
  exact ⟨by omega,by omega,by omega,max_lt (max_lt (by omega) en) ek,nsmall,sender_keys ..,
    by omega,by omega,by omega,by omega⟩

end
end Hierarchy.DescentDatedAddressBook.ResetMiddle

end OAI
