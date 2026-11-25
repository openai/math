import OAI.Hierarchy.DescentOrdinaryPeerCount
import OAI.Hierarchy.DescentDatedAddressRate

namespace OAI
/-! # Space for the actual ordinary successor's roster, host count and hub bits -/
namespace Hierarchy.DescentOrdinaryVenueReturn
open DescentDyadicSpan DescentDatedAddressBook ProtocolRAM
def bookStart (base H D R E:ℕ):=DescentOrdinaryPeerCount.roof base H D R E
def owners (base H D R E:ℕ):Bank:=⟨bookStart base H D R E,Nat.clog 2 R⟩
def masks (base H D R E:ℕ):Bank:=⟨bookStart base H D R E+span R,Nat.clog 2 R⟩
def hubs (base H D R E:ℕ):Bank:=⟨bookStart base H D R E+2*span R,Nat.clog 2 R⟩
def roof (base H D R E:ℕ):=(hubs base H D R E).base+span R
theorem expanded (base H D R E:ℕ):
    roof base H D R E=base+span (H*(D+1)^10)+3*span (R*E)+span H+span (R*E)+1+3*span R:=by
  simp only [roof,hubs,bookStart,DescentOrdinaryPeerCount.roof,DescentOrdinaryPeerRows.endAddress,
    DescentOrdinaryPeerChart.top,DescentOrdinaryPeerChart.out,DescentOrdinaryPeerChart.length,
    DescentOrdinaryPeerRows.fixed,DescentTenHopRAM.paths]
  omega
theorem shift (base H D R E:ℕ):roof base H D R E=base+roof 0 H D R E:=by rw [expanded,expanded];omega

variable {ι:ℕ→Type*} {H D R E:∀h,ι h→ℕ}
theorem rate (hosts:Bounded H)(deg:Bounded D)(newHosts:Bounded R)(newDeg:Bounded E):
    Bounded (fun h i=>roof 0 (H h i) (D h i) (R h i) (E h i)):=by
  have one:=Bounded.const (ι:=ι) 1
  have three:=Bounded.const (ι:=ι) 3
  have reach:=(hosts.mul ((deg.add one).pow 10)).padded
  have next_:=(newHosts.mul newDeg).padded
  apply (((((reach.add (three.mul next_)).add hosts.padded).add next_).add one).add (three.mul newHosts.padded)).of_le
  intro h i; rw [expanded];simp [span]
end Hierarchy.DescentOrdinaryVenueReturn

end OAI
