import OAI.Hierarchy.DescentVenueSlabs
import OAI.Hierarchy.DescentOverlapTariff
import OAI.Hierarchy.DescentColumnHardware

namespace OAI
/-! Native cost of changing the packing width of a rectangular bank. -/
namespace Hierarchy.DescentVenueSlabs
open DescentSIMDLookup ProtocolRAM ProbeStage.Native
open DescentStaticWordColumn (names names_seq)
noncomputable section
variable (s:Shape)
local notation "oldN" => s.hosts*chunks s.groups s.sourceLanes
local notation "ps" => s.pages*s.hosts
def tariff :=
  (4+s.pages*(4+oldN*18)) + 7*(15+s.pages*39)+
  2048*((Overlap.pieces s.groups s.sourceLanes s.targetLanes+1)*(s.sourceLanes+1)*2^(s.bits*s.sourceLanes)+
    Overlap.rows ps s.groups s.sourceLanes+Overlap.rows ps s.groups s.targetLanes+1)

theorem price (pages:Fin s.pages→Bank) (base w:ℕ) (positive:0<s.sourceLanes) (next:0<s.targetLanes) :
    ticks s pages base+7*names (program s pages base w)≤tariff s:=by
  let es:=exprs s pages
  have length_:es.length=s.pages:=by simp [es,exprs]
  have bound:∀e∈es,e.work≤7:=by
    intro e he
    obtain ⟨j,rfl⟩:=List.mem_ofFn.mp he
    exact Nat.le_refl 7
  have clock:=columns_clock oldN base 7 es bound
  have names_:=DescentOrdinaryAtomFieldRAM.ScalarOperand.labels_registers es base oldN 7 w bound
  change names (ProtocolRAM.program w (passes s pages base))≤15+es.length*(11+4*7) at names_
  have main:=Overlap.tariff (work s base) ps s.groups s.sourceLanes s.targetLanes s.bits w (gathered s base) positive next
  rw [program,names_seq,ticks,tariff]
  simp only [length_,show 2*7+4=18 from rfl,show 11+4*7=39 from rfl] at clock names_
  change ProtocolRAM.clock (passes s pages base)≤_ at clock
  omega

end
end Hierarchy.DescentVenueSlabs

end OAI
