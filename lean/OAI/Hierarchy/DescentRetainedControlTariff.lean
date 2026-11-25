import OAI.Hierarchy.DescentRetainedControlRun
import OAI.Hierarchy.DescentRetainedMoveTariff

namespace OAI
/-! # Hardware and clock for the measured per-primary route -/
namespace Hierarchy.DescentRetainedControl.Layout
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentResetRetainedSetup
open DescentResetRetainedSetup.Layout DescentSixParty.Chronology
open DescentStaticWordColumn (names names_seq)
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
noncomputable section
variable (s : DescentRetainedControl.Layout)
def invoice (readWork : ℕ):=
  let d:=readWork+12
  mountFee (s.targets*(2*2^(s.rootWidth*s.oldLanes)))+
    ((4+s.targets*(4+s.rows*(2*d+4)))+7*(15+s.targets*(11+4*d)))+
    (109+s.targets*stripCharge s.hosts s.groups s.oldLanes s.lanes s.selectorBits)+
    mountFee ((2*s.targets)*(2*2^(s.aperture*s.lanes)))

theorem tariff (base w : ℕ) (which : s.Targets) (packet : Expr) (T : ℕ) (fit : packet.work≤T)
    (old : 0<s.oldLanes) (fresh : 0<s.lanes) :
    s.ticks which base w packet+7*names (s.program which base w packet)≤ s.invoice T:=by
  let terms:=List.ofFn (s.readControl which base packet)
  have budget (e : Expr) (inList : e∈terms):e.work≤T+12:=by
    obtain ⟨j,rfl⟩:=List.mem_ofFn.mp inList
    change (Tables.read _ packet (.lit 0)).work≤T+12
    simp only [Tables.read,Expr.work]
    omega
  have scanned:=ProbeStage.Native.columns_clock s.rows (s.installed base) (T+12) terms budget
  have named:=ProbeStage.Native.columns_text w s.rows (s.installed base) (T+12) terms budget
  change names (ProtocolRAM.program w (s.scans which base packet))≤_ at named
  change clock (s.scans which base packet)≤_ at scanned
  have len : terms.length=s.targets:=List.length_ofFn
  rw [len] at scanned named
  have packed:=strip_cost (s.temporary base) s.hosts s.groups s.oldLanes s.lanes s.selectorBits w (s.temp base) old fresh
  change (s.retile base w).ticks+7*names (s.retile base w).program≤_ at packed
  simp only [ticks,program,names_seq,stage₁,stage₂,Book.names,invoice,mountFee]
  omega

theorem channel_work (which : s.Targets) (base : ℕ) (t : Fin s.targets) (o : Bank) :
    (s.targetStream which base t (.lookup o .row)).work≤25:=by rfl

end
end Hierarchy.DescentRetainedControl.Layout

end OAI
