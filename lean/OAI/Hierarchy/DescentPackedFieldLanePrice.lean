import OAI.Hierarchy.DescentPackedRegroup
import OAI.Hierarchy.DescentPackedPrivateAccumulator

namespace OAI
/-! # The private counter reads the producer's wider register format without changing lane order -/
namespace Hierarchy.DescentPackedPrivateSum.Layout
open DescentSIMDLookup

theorem tariff_wide (w H r short full : ℕ) (positive : 0<full) (inside : short≤full) (wide : 2*full≤w) :
    billed H r (lanes w full)*w≤40*(w+H*w+4*H*r*full) ∧
    2^(short*lanes w full)≤2^(w/2) := by
  obtain ⟨bill,table⟩:=tariff w H r full positive wide
  exact ⟨bill,(Nat.pow_le_pow_right (by decide : 0<2) (Nat.mul_le_mul_right _ inside)).trans table⟩

end Hierarchy.DescentPackedPrivateSum.Layout

namespace Hierarchy.DescentPackedPrivateAccumulator
open DescentSIMDLookup DescentPackedPrivateSum

theorem tariff_wide (C : Counters) (w H r short full grain : ℕ) (positive : 0<full)
    (inside : short≤full) (wide : 2*full≤w) :
    (Layout.billed H r (lanes w full)+C.scaling.steps grain)*w≤
      40*(w+H*w+4*H*r*full)+(56+4*ProtocolRAMPortScale.bitWidth grain)*w ∧
    2^(short*lanes w full)≤2^(w/2) := by
  obtain ⟨bill,table⟩:=Layout.tariff_wide w H r short full positive inside wide
  rw [Nat.add_mul,DescentPrivateExponentRAM.steps_eq]
  exact ⟨Nat.add_le_add_right bill _,table⟩

end Hierarchy.DescentPackedPrivateAccumulator

namespace Hierarchy.DescentSixParty.Chronology
open DescentPackedPrivateAccumulator DescentPackedPrivateSum DescentSIMDLookup

/-- A donor lookup and the subsequent addition of all eleven cable roles scan one
word per original donor chunk. The scoring ROM is at most half-word exponential. -/
theorem donor_stage_tariff (C : Counters) (w H J full short grain : ℕ)
    (positive : 0<full) (inside : short*11≤full) (wide : 2*full≤w) :
    let m:=lanes w full
    ((4+44*(H*chunks J m))+(Layout.billed H (J*11) (m*11)+C.scaling.steps grain))*w≤
      (21+(56+4*ProtocolRAMPortScale.bitWidth grain))*w+84*(H*w+4*H*J*full) ∧
    2^(short*(m*11))≤2^(w/2) := by
  dsimp only
  have pos:0<lanes w full := (occupancy w full positive wide).1
  have vol:=volume H J w full positive wide
  have rom:=(Layout.tariff_wide w H J (short*11) full positive inside wide).2
  constructor
  · simp only [Layout.billed,Layout.count,chunks_group J (lanes w full) 11 pos (by decide),
      DescentPrivateExponentRAM.steps_eq]
    nlinarith only [Nat.mul_le_mul_left 84 vol]
  · simpa [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using rom

end Hierarchy.DescentSixParty.Chronology

end OAI
