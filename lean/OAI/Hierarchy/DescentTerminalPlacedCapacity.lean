import OAI.Hierarchy.DescentTerminalExteriorPacketBill
import OAI.Hierarchy.DescentTerminalCalibratedRowArithmetic
import OAI.Hierarchy.DescentTerminalPlacedNames
import OAI.Hierarchy.DescentTerminalIntegralFrontier

namespace OAI
/-! # Public terminal capacities for the actual packed graph budget -/
namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan
open DescentTerminalGraphVolume DescentTerminalEmitter DescentTerminalRowArena DescentSixParty
noncomputable section

/-- The old dense assignment is zero-extended by computing one final page;
the public side uses the true number of complete dyadic slabs. -/
def dimensions (hosts:ℕ) (positive:0<hosts) (slots W total socket e j r t:ℕ) : Shape :=
  let rows:=bought slots W
  let packets:=e*2^(j+r)
  ⟨0,0,0,hosts,positive,⟨⟨e,j,r,t,total/socket+1,packets,rows⟩,rows,rows,rows⟩⟩

variable {p q W total exterior hosts : ℕ} (pos:0<hosts) (width:0<W)
local notation "budget" => rowBudget p q W total exterior hosts 3
local notation "billed" => bought budget W
variable (e j r t:ℕ)
local notation "S" => dimensions hosts pos budget W total (q*p) e j r t

include width in
theorem genuine_caps (I:Input) (base:ℕ) (O:DescentPrivateExponentRAM.Banks)
    (i:I.indexEvents≤2*billed) (f:I.formatEvents≤2*billed) : RowCap S (layout S I base O) billed := by
  have enough: W≤budget:=by unfold rowBudget;omega
  have purchased : budget ≤ billed := (cap_both width enough).1
  have num:total≤3*(2*total+exterior):=by omega
  have div:=Nat.div_le_div_right (c:=q*p) num
  have spare : total/(q*p)+2 ≤ billed := by
    apply Nat.le_trans _ purchased
    unfold rowBudget
    omega
  have expand:=DescentTerminalDataPlane.Arena.cost (total/(q*p)+1+2+(e*2^(j+r)+2))
  constructor
  · exact le_rfl
  · exact le_rfl
  · exact le_rfl
  · change DescentTerminalDataPlane.Arena.size (total/(q*p)+1+2+(e*2^(j+r)+2))≤2*(billed+(e*2^(j+r))+4)
    omega
  · change e*2^(j+r)≤e*2^(j+r)+2;omega
  · exact Nat.le_succ _
  · exact le_rfl
  · exact le_rfl
  · exact i
  · exact f

end
end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan

end OAI
