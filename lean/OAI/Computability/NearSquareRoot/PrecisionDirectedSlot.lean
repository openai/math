import OAI.Computability.NearSquareRoot.PrecisionSlotSchedule
import OAI.Computability.NearSquareRoot.SynchronizedBoxPlanProgram

/-! # Phase queries from the generated forward or inverse block schedule -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhaseTable

open IntegerMultiplication Code Strip Staff ShortFourier.BatchWord

/-- The serialized physical schedule is generated from just the global address
width and its direction bit in the same setup regime as its coefficient rows. -/
theorem prepareScheduledBlock {I : Type} {s : Regime I} {k stage block bits : I → ℕ}
    {inverse : I → Bool} (K : Realizes s k) (F : s.Has inverse)
    (P : Realizes s bits) (T : Realizes s stage) (B : Realizes s block)
    (f : I → SlotDescriptor → ℂ)
    (payload : ∀ (v : I → SlotDescriptor), s.Has v → Prepared s bits (fun j ↦ f j (v j))) :
    Prepared s bits (fun j ↦
      let query := directedQuery (directedPlan (inverse j,tally (k j))) (stage j) (block j)
      adjointValue query.1 (query.2.elim 1 (f j))) := by
  have H := (Regime.Has.pair F K).thenDo directedPlan_poly
  exact prepareDirectedQuery P (([],[],ShortFourier.AxisWord.inst 0),[]) H T B f payload

end PhaseTable

end NearSquareRoot
end Computability
end OAI
