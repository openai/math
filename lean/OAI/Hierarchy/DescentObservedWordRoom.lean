import OAI.Hierarchy.DescentPublicObservedWordRoom
import OAI.Hierarchy.DescentDatedScheduleRoom
import OAI.Hierarchy.DescentChronologicalCapacity

namespace OAI
/-! # Sufficient word width for the raw host/group/block key and true core count -/
namespace Hierarchy.DescentSixParty
open DescentCompiler DescentCompiler.TerminalScale
noncomputable section
variable {F P : Type} [Field F] {G : PoweredGadget F} {S : AtomSchedule} {dim k i z D wire hist : ℕ}
    {bits : P→ℕ} {q ε : ℝ} {W : MarkedWorld F dim P bits}

theorem Reached.core_padded (r : Reached W G q ε S k i z D wire hist) :
    W.core.card≤(S.groupCount i*hostRows (S.hostSize i)*2^k)*2^(8+S.capGain*i) := by
  let A:=r.placement
  have census:=W.census_paid W.core A.pos A.block (fun v=>A.hub (A.pos v).2) A.records A.wire A.hist
    (A.z*G.b) A.cap A.wirePos (Nat.mul_pos A.unitPos G.base_pos) (fun e he=>(A.widths e he).ge) A.small
  have sites : Fintype.card r.V≤hostRows (S.hostSize i) := r.valid.host.trans (hostPad _)
  have count : Fintype.card (Fin (S.groupCount i)×r.V)*2^k≤S.groupCount i*hostRows (S.hostSize i)*2^k := by
    simpa [Fintype.card_prod] using Nat.mul_le_mul_right (2^k) (Nat.mul_le_mul_left (S.groupCount i) sites)
  exact census.trans (Nat.mul_le_mul count r.valid.capacity)

end
end Hierarchy.DescentSixParty

end OAI
