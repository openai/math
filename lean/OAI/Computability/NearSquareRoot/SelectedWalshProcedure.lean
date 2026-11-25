import OAI.Computability.NearSquareRoot.SelectedWalshRowProfile
import OAI.Computability.NearSquareRoot.SelectedKernelProfiles

/-! # The Walsh source files used by the guarded multiplication scheduler -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedCandidate.CandidateParameters

open Filter FixedLayer SynchronizedPermutationBudget

/-- Both directions use the physical selected rows at the common integer-input
cutoff. The three reserve estimates are resources of the literal tuple. -/
theorem walshProcedure (F : InterchangeROMFamily.NativeFamily) (degree : ℕ) (dir : Bool) :
    Nonempty (Procedure degree (.walsh dir)) := by
  obtain ⟨arena,clock,run,_,bounds⟩ := selectedWalshRowProfile F degree dir
  refine ⟨⟨arena,clock,run,fun j => ?_⟩⟩
  filter_upwards [bounds j] with a ha
  filter_upwards [ha] with b hb
  filter_upwards [hb] with d hd
  refine ⟨⟨1,?_⟩,hd.2⟩
  filter_upwards [hd.1] with w hw
  simp [hw]

end FixedCandidate.CandidateParameters

end NearSquareRoot
end Computability
end OAI
