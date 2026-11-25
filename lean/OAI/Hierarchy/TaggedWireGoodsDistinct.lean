import OAI.Hierarchy.ProbeCoreWalks

namespace OAI
/-! # Distinct ends of every payload and signed comparison commodity -/

namespace Hierarchy.ProbeStage.CoreBoard
open AdaptiveProbe
variable {h d k : ℕ}
theorem goods_different (π : Equiv.Perm (Fin (2^h))) (i : Commodity (Fin (2^h)) (Stages h d) k) :
    (commodityEnds π i).1≠(commodityEnds π i).2 := by
  rcases i with p|⟨⟨p,t⟩,l⟩
  · simp [commodityEnds]
  · simp [commodityEnds,inputCol,outputCol]

end Hierarchy.ProbeStage.CoreBoard

end OAI
