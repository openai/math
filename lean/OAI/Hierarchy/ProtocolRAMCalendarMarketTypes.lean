import OAI.Hierarchy.ProtocolRAMPurchaseShelfGeometry
import OAI.Hierarchy.ProtocolRAMPrices
import OAI.Hierarchy.ProtocolRAMFailureWords

namespace OAI
/-! # Fixed calendar market dimensions and the incoming permutation bank -/

namespace Hierarchy.ProtocolRAM.Calendar
open ProbeStage ProbeStage.Native PurchaseCT ProtocolRAMPurchaseAllocation PurchaseFrozen
noncomputable section
variable {z d k : ℕ}

/-- The permutation and signed potential certify the initial physical table words.
Only the shelf locations and the fixed sampler/depth occur in executable code. -/
structure Market (z d k : ℕ) where
  sampler : PurchaseSampler
  depth : ℕ
  phase : PhasePrice
  temperature : ℝ
  kind : ℕ
  shelf : Shelf
  failures : FailureWords

def Market.flags (v : Market z d k) := v.shelf.flagsBase v.sampler z d k v.depth

def Market.rows (v : Market z d k) := count z d k*paths z v.sampler.degree v.depth

namespace Boot

theorem root_extent : 2^z≤heapEnd z d copies := by
  have small : 2^z≤extent z d := Nat.pow_le_pow_right (by decide) (by unfold roomBits; omega)
  have bound := phase_in_heap (h:=z) (d:=d) (copies:=copies) (Nat.zero_le (rounds d))
  simp only [ProbeStage.Native.phase,Nat.zero_mul,Nat.add_zero] at bound
  omega

end Boot
end
end Hierarchy.ProtocolRAM.Calendar

end OAI
