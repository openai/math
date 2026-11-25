import OAI.Hierarchy.DescentPackedDonorTables

namespace OAI
/-! # Invoice for donor words already grouped by their source publisher -/
namespace Hierarchy.DescentPackedDonorTables
open DescentPackedPrivateSum DescentPackedPrivateAccumulator DescentSIMDLookup

theorem grouped_pages {payload a b M : ℕ} (fit : M*max a (b*11)≤payload/2) :
    2^(a*M)≤2^(payload/2) ∧ 2^(b*(M*11))≤2^(payload/2) := by
  constructor
  · apply Nat.pow_le_pow_right (by decide)
    rw [Nat.mul_comm]
    exact (Nat.mul_le_mul_left _ (Nat.le_max_left ..)).trans fit
  · apply Nat.pow_le_pow_right (by decide)
    rw [show b*(M*11)=M*(b*11) by ring]
    exact (Nat.mul_le_mul_left _ (Nat.le_max_right ..)).trans fit

/-- No occupancy lower bound is needed. The counted main scan matches exactly
the number of words actually written by the predecessor. -/
theorem grouped_price (base payload H J a b grain M : ℕ) (C : Counters)
    (live : 0<M) (fit : M*max a (b*11)≤payload/2) :
    let pages:=size (DescentPackedDonorSpace.banks base H J M a)
      (DescentPackedDonorSpace.layout base H J M a b).rom.base b M
    (4+10*pages)+((4+44*(H*chunks J M))+(Layout.billed H (J*11) (M*11)+C.scaling.steps grain))≤
      131+4*ProtocolRAMPortScale.bitWidth grain+124*(H*chunks J M)+20*2^(payload/2) := by
  obtain ⟨front,back⟩:=grouped_pages fit
  have pageCount:=arena_size base H J M a b live
  simp only [Layout.billed,Layout.count,chunks_group J M 11 live (by decide),DescentPrivateExponentRAM.steps_eq]
  omega


end Hierarchy.DescentPackedDonorTables

end OAI
