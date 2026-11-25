import OAI.Hierarchy.DescentSeedFirstDonorRate
import OAI.Hierarchy.DescentDateLaneAmount
import OAI.Hierarchy.DescentSeedNumberRates

namespace OAI
/-! # Actual first ordinary donor width before choosing the parameter cutoff -/
namespace Hierarchy.DescentDatedSeedStartup
open DescentCompiler DescentCompiler.TerminalScale DescentSixParty DescentSixParty.Chronology
variable {F : Type} [Field F] (G : PoweredGadget F)

theorem first_donor_rate (t f g reset : ℕ) :
    ∃a : ℕ,∀ J M tail p : ℕ,
      let S:=stageNumbers G t J f g reset M tail
      let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
      (DonorDate.atDate G S g k 0 p).amount ≤ scale J a := by
  obtain ⟨a, bound⟩ := first_donor_amount_rate G t f g reset
  refine ⟨a, ?_⟩
  intro J M tail p S k
  have degree : (DonorDate.atDate G S g k 0 p).degree = originalDegree G S g := rfl
  have cap : (DonorDate.atDate G S g k 0 p).cap = 256 := by
    simp [DonorDate.atDate, DescentPacking.PackedMatch.Local.Stage.Dated.forAge]
  calc
    _ = donorAmount k (originalDegree G S g) 256 G.b G.C G.k := by
      rw [DonorDate.atDate_amount, degree, cap]
    _ ≤ _ := bound J M tail p

end Hierarchy.DescentDatedSeedStartup

end OAI
