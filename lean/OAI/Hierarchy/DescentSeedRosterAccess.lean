import OAI.Hierarchy.DescentSeedInitialTable

namespace OAI
/-! # Sizes and disjoint native ranges of all initial directories -/
namespace Hierarchy.DescentSeedInitialTable
open DescentSIMDLookup DescentPackedColony ProtocolRAM
noncomputable section

theorem accessible (base H G M D w floor : ℕ)
    (stop : endAddress base H G M D ≤ floor) (room : floor<2^w) :
    Accessible (ports base H G M D) (bank base H G M D 3) H G M w floor := by
  let project (c : ℕ) (hc : c<D+8) : (bank base H G M D c).Fits w floor := by
    have fit:=bank_fits hc (stop.trans_lt room)
    exact ⟨fit.1,fit.2.1,fit.2.2.trans stop⟩
  obtain ⟨hc,hd,hr⟩:=capacities H G M D
  exact ⟨fun i=>project (8+i.val) (by omega), fun _=>hr,project 0 (by omega), hd,
    project 1 (by omega),hc,project 2 (by omega),hr,project 3 (by omega),hr⟩

end
end Hierarchy.DescentSeedInitialTable

end OAI
