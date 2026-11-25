import OAI.Hierarchy.DescentSeedInitialTable

namespace OAI
/-! # The one-word host-count column inside the padded source roster -/
namespace Hierarchy.DescentSeedInitialTable
open ProtocolRAM
noncomputable section

/-- The guard word after all public host queries in the hub column. -/
def sharedHostCountBank (base H G M : ℕ) : Bank := ⟨(bank base H G M 3 4).base+H,0⟩

theorem shared_host_slot (H G M : ℕ) : H<stride H G M 3 :=by
  have cap:=(capacities H G M 3).2.1
  have pos : 0<stride H G M 3:=Nat.two_pow_pos _
  omega

theorem shared_host_fits (base H G M w : ℕ) (space : endAddress base H G M 3<2^w) :
    (sharedHostCountBank base H G M).Fits w (endAddress base H G M 3) :=by
  let r:=stride H G M 3
  have inside : H<r:=shared_host_slot H G M
  change base+11*r<2^w at space
  change 0<1 ∧ 1<2^w ∧ base+4*r+H+1≤base+11*r
  omega

end
end Hierarchy.DescentSeedInitialTable

end OAI
