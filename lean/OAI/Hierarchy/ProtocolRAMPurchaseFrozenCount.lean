import OAI.Hierarchy.ProbePermutationRoute
import OAI.Hierarchy.ProbeStageScale

namespace OAI
/-! # Fixed source and path counts for a purchase snapshot -/

noncomputable section
namespace Hierarchy.ProtocolRAM.PurchaseFrozen
open ProbeStage

def count (z d k : ℕ) := (permutationFabric z d).shapes.length*(2*k)

theorem count_eq (z d k : ℕ) : count z d k=(2*rounds d+1)*(2*k) := by
  rw [count,show (permutationFabric z d).shapes.length=2*rounds d+1 from template_length ..]

def paths (z D depth : ℕ) := 2^z*D^depth

end Hierarchy.ProtocolRAM.PurchaseFrozen
end

end OAI
