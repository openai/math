import OAI.Hierarchy.DescentCapAtAge
import OAI.Hierarchy.DescentSeedDonorRate
import OAI.Hierarchy.DescentIncomingCalendarFactors

namespace OAI
/-! # Actual donor unit on every fixed original public date -/
namespace Hierarchy.DescentSixParty.NativePitch
open DescentCompiler DescentCompiler.TerminalScale DescentDatedSeedStartup DescentHostDegree Chronology
open scoped BigOperators
variable {F:Type} [Field F] (G:PoweredGadget F)

theorem all_donor_rate (t f g reset:ℕ):
    ∃a:ℕ,∀J copies tail p i:ℕ,
      let S:=stageNumbers G t J f g reset copies tail
      let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
      0<(DonorDate.atDate G S g k i p).amount ∧ (DonorDate.atDate G S g k i p).amount≤ scale J a:=by
  obtain ⟨_,a,rates⟩:=donor_uniform t (hostRate t reset) (capRate G t g) (cutRate t f g)
    (initialDegreeMax t) G.b G.C G.k
  refine ⟨a,?_⟩;intro J copies tail p i S k
  let d:=DonorDate.atDate G S g k i p
  refine ⟨(Nat.succ_pos _).trans_le ((Nat.le_max_right ..).trans (Nat.le_max_right ..)),?_⟩
  rw [DonorDate.atDate_amount]
  exact (rates J d.degree d.cap (seed_degree _ _ _) (all_caps G t g J i)).2

end Hierarchy.DescentSixParty.NativePitch

end OAI
