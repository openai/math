import OAI.Computability.BorderVNP.DiagonalNativeProfileDirectory
import OAI.Computability.BorderVNP.RoutingISASignedPrepCoupling

/-! # Every returning pre-call path has a genuine decoded geometry history -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots

open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator RoutingISA.CompactMachine
open PackedHistoryCircuit CellMacro.Generator BorderVNP.Cube BorderVNP.Cube.Tally
open private before_iff from OAI.Computability.BorderVNP.DiagonalNativePublishedWindow

variable {dim box lanes selectors symbols n w k : ℕ} {id : TableEntry dim box lanes selectors symbols → ℕ}
    {gen : Fragment IO} {pub : Arg → Word w} {routines : TeamOpcode.Macros w 8}
    (f : BroadcastFrame) {bank : Bank w} {initial : Memory w} {trace z saved}
local notation "mac" => install gen n routines

/-- The public history check occurs before all private cells and before any
subtotal test. Extract its genuine returning execution from an arbitrary
returned pre-call path, even when that path's future contribution vanishes. -/
theorem profile_from_preparation (boot : Runs pub mac JointHeader.bootHeader bank initial trace z saved)
    (stable : f.Stable (readings z)) (positive : (saved f.dst).val ≠ 0)
    (pins : (Fin k → Bool) ≃ Pins.Return pub mac (Function.update z 10 (saved f.dst)) saved)
    (bits : Fin k → Bool) (p : SignedPreps id pub routines gen n _ saved pins bits) :
    Nonempty (Returns (withStartup pinGeometry) pub mac bank initial) := by
  let stages := (SignedPrep.visitsEquiv id pub mac (pins bits).val.2.1 (pins bits).val.2.2).symm p
  obtain ⟨g,mg,ge,_,_,geo,_⟩ := Runs.seq_iff.mp ((before_iff dim (selectorWidth dim selectors lanes)).mp stages.profile.property)
  obtain ⟨_,_,pre,head,_,start,copy⟩ := Runs.seq_iff.mp boot
  exact ⟨⟨(dispatchPrefix f saved pre head++((pins bits).val.1++ge),g,mg),
    (evaluation_startup_iff f pinGeometry start copy stable positive).mpr ⟨_,rfl,(pins bits).property.seq geo⟩⟩⟩

end TeamContraction.ProcessorSlots

end BorderVNP
end Computability
end OAI
