import OAI.Hierarchy.DescentTerminalPlacedClock
import OAI.Hierarchy.DescentTerminalRowArenaHigh
import OAI.Hierarchy.DescentTerminalRowArenaSortHigh

namespace OAI
/-! # The mounted exterior transcript survives every bounded row and site scan -/
namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentTerminalRowArena DescentTerminalVertexFields
open ThreeFlat.RAM PhysicalProcedure
open DescentTerminalDataPlane.Arena (buy size)
noncomputable section
variable {blocks w:ℕ} (S:Shape) (I:Input) (base:ℕ) (F:MaskedShelf blocks) (O:DescentPrivateExponentRAM.Banks)
local notation "A" => rowArena S I base
local notation "L" => layout S I base O
local notation "p" => S.terminal.pool

theorem mounted_high (m:Memory w) {x:ℕ} (above:(A).finish≤x) : (A).mount m x=m x := by
  have width:=(A).stride_min
  have cap:2*(A).sites+_+_+1<(A).stride:=width
  change (A).start+22*(A).stride≤x at above
  have no0:¬((A).atBand 0≤x ∧ x<(A).atBand 0+2*(A).sites):=by change ¬(_≤x ∧ x<(A).start+0*(A).stride+2*(A).sites);omega
  have no1:¬((A).atBand 1≤x ∧ x<(A).atBand 1+2*(A).sites):=by change ¬(_≤x ∧ x<(A).start+1*(A).stride+2*(A).sites);omega
  simp only [Arena.mount,fillSegment,ite_eq_right no0,ite_eq_right no1]

/-- Ranks, stable packet sorting, masked page writes and leaf issuance all finish
below the first mounted public word. This covers exterior data and flags in high memory. -/
theorem events_after (m:Memory w) (low:Earlier S I base F w) (fit:endAddress S I base<2^w)
    {x:ℕ} (high:pageEnd S I base≤x) :
    Suffix.events S L F ((A).mount m) x=m x := by
  obtain ⟨p0,p1,p2,p3,p4⟩:=stages S I base
  have finish:=p0.trans high
  have addr:=p0.trans_lt (p1.trans_lt (p2.trans_lt (p3.trans_lt (p4.trans_lt fit))))
  have endPage : (page A).base+(page A).size≤pageEnd S I base:=Nat.le_add_right ..
  have siteCount:S.sites+1≤(page A).size:=Nat.le_of_lt (DescentTerminalDataPlane.Arena.room _)
  have rows:p≤(events A p).size:=Nat.le_of_lt (DescentTerminalDataPlane.Arena.room _)
  have printed:(L).emit.leaf.event.base=(events A p).base:=by change (inputs S I base 40).base=_;simp [inputs]
  have rawEnd:(events A p).base+(events A p).size≤x:=high
  have pageEnd_:(page A).base+(page A).size≤x:=endPage.trans high
  have page_:¬((L).directory.texture.base≤x ∧ x<(L).directory.texture.base+(S.sites+1)):=by
    change ¬((page A).base≤x ∧ x<(page A).base+(S.sites+1));omega
  have event_:¬((L).emit.leaf.event.base≤x ∧ x<(L).emit.leaf.event.base+p):=by rw [printed];omega
  unfold Suffix.events DescentTerminalEmitter.issued Suffix.pages maskedMem
  simp only [ProtocolRAM.image,fillSegment,ite_eq_right event_,ite_eq_right page_]
  have sorting:=(A).sockets_after (DescentTerminalRowPlan.result (A).row (A).sites (A).rows ((A).mount m)) S.sites_pos low.old addr finish
  exact sorting.trans (((A).plan_after ((A).mount m) addr finish).trans (mounted_high S I base m finish))

end
end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan

end OAI
