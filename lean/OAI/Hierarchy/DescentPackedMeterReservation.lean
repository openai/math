import OAI.Hierarchy.DescentPackedDonorSpace

namespace OAI
/-! # The counter's actual output lies before the end of the donor reservation -/
namespace Hierarchy.DescentSixParty.Chronology.DonorSpace
open DescentSIMDLookup
theorem reserved_counter (start H G M radix payload input short : ℕ) (live : 0<M)
    (positive : 0<radix) (inRoom : input*(M*radix)≤payload/2) (outRoom : short*((M*radix)*11)≤payload/2) :
    DescentPackedDonorSpace.endAt start H (G*radix) (M*radix) input short≤
      start+8*(H*chunks G M)+2*2^(payload/2)+12 :=by
  have bound:=DescentPackedDonorSpace.footprint start H (G*radix) (M*radix)
    input short (Nat.mul_pos live positive)
  rw [chunks_group G M radix live positive] at bound
  have lo:=Nat.pow_le_pow_right (by decide : 0<2) inRoom
  have hi:=Nat.pow_le_pow_right (by decide : 0<2) outRoom
  omega
end Hierarchy.DescentSixParty.Chronology.DonorSpace

end OAI
