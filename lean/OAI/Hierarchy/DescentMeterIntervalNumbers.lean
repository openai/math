import OAI.Hierarchy.DescentPackedDonorSpace

namespace OAI
/-! # The literal private counter arena is above its input, including an empty donor row -/
namespace Hierarchy.DescentPackedDonorSpace
open ProtocolRAM DescentSIMDLookup DescentPackedPrivateSum DescentPackedPrivateAccumulator

theorem chunks_replicate_le (J M count : ℕ) :
    chunks (J*count) (M*count)≤chunks J M :=by
  by_cases h : M=0
  · subst M;change _ / (0*count)≤_ / 0;simp
  by_cases c : count=0
  · subst count;change _ / (M*0)≤_;simp
  exact (chunks_group J M count (by omega) (by omega)).le

theorem footprint_all (base H J M input short : ℕ) :
    endAt base H J M input short≤base+8*(H*chunks J M)+2^(input*M)+2^(short*(M*11))+11 :=by
  have first:=(DescentPackedPrivateSpace.source_size base H J M).2
  have bound:=DescentPackedPrivateSpace.footprint (consumerBase base H J M input) H (J*11) (M*11) short
  let sz:=(DescentPackedPrivateSpace.source base H J M).size
  change sz≤2*(H*chunks J M+1) at first
  change endAt base H J M input short ≤base+1+sz+sz+2^(input*M)+4*(H*chunks (J*11) (M*11))+2^(short*(M*11))+6 at bound
  have pack:=Nat.mul_le_mul_left H (chunks_replicate_le J M 11)
  omega

theorem above (base H J M input short : ℕ) :
    base<endAt base H J M input short :=by
  unfold endAt consumerBase banks DescentPackedPrivateSpace.endAt DescentPackedPrivateSpace.counters
    DescentPackedPrivateSpace.layout DescentPackedPrivateSpace.rom DescentPackedPrivateSpace.source
  dsimp only
  omega

/-- Packed output roles share the original row count. Both immutable lookup pages
are bounded by half of the payload, even for an empty or malformed public bank. -/
theorem grouped_end (base H J count input short amount payload : ℕ)
    (field : count*max input (short*11)≤amount) :
    let M:=lanes payload amount
    endAt base H (J*count) (M*count) input short≤
      base+8*(H*chunks J M)+2*2^(payload/2)+12 :=by
  intro M
  have room : (M*count)*max input (short*11)≤payload/2:=by
    rw [Nat.mul_assoc]
    exact (Nat.mul_le_mul_left M field).trans (lanes_fit payload amount)
  have first : input*(M*count)≤payload/2:=by
    rw [Nat.mul_comm];exact (Nat.mul_le_mul_left (M*count) (le_max_left ..)).trans room
  have last : short*((M*count)*11)≤payload/2:=by
    calc _=(M*count)*(short*11):=by ring
         _≤_ := (Nat.mul_le_mul_left (M*count) (le_max_right ..)).trans room
  have rows:=Nat.mul_le_mul_left H (chunks_replicate_le J M count)
  have cap:=footprint_all base H (J*count) (M*count) input short
  have a:=Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) first
  have b:=Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) last
  omega

end Hierarchy.DescentPackedDonorSpace

end OAI
