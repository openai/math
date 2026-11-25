import OAI.Hierarchy.DescentDatedMeterCode
import OAI.Hierarchy.DescentPrivateNativeDate
import OAI.Hierarchy.DescentDatedOrdinaryArea

namespace OAI
/-! # The unconditional public machine for a private-meter date -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage.Dated
open DescentSixParty DescentSixParty.Chronology DescentHostDegree DescentPackedPrivateSum
open DescentRawCablePanel DescentSIMDLookup Computability.VPVNP.BurstRAM
open ThreeFlat.RAM PhysicalProcedure
noncomputable section

namespace Meter
def ofOrdinary (a : Ordinary) (radix ceiling padding quantum groupLanes base header : ℕ) : Meter :=
  ⟨a.H,a.G,a.k,a.D,a.cap,radix,ceiling,padding,quantum,groupLanes,base,header⟩

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
variable {S : DescentCompiler.AtomSchedule} {q fee u : ℝ} {k i z D wire hist : ℕ}
variable {W : MarkedWorld F d P bits} {src : Reached W G q fee S k i z D wire hist}
variable {he : 0≤fee} {T : StageInput W G u fee} {c : (T.result he).Choice} {n : Normalize ((T.result he).state c)}
variable {z' D' : ℕ} {dst : Reached n.result G q fee S k (i+1) z' D' wire hist}
variable (ticket : OrdinaryLink src he T c n dst) (port : MeterPort src) (header : ℕ)

/-- Numeric projection before using the public named slot/degree calculation. -/
def ofTicket : Meter :=
  ⟨port.hosts,S.groupCount i,k,src.placement.degree,src.placement.cap,G.b,G.C,G.k,T.z,port.groupsPerWord,port.base,header⟩

include ticket in
theorem ticket_shape : T.k=k ∧ T.Δ=src.placement.degree := by
  have rate:=ticket.sourceRate
  subst u
  have eqn : T=src.placement.stage:=eq_of_heq ticket.placement
  cases eqn
  exact ⟨rfl,rfl⟩

theorem ticket_code (w : ℕ) :
    MeterPort.program ticket port header w=(ofTicket (T:=T) port header).program w ∧
    MeterPort.ticks ticket port header=(ofTicket (T:=T) port header).ticks ∧
    MeterPort.hardware ticket port=(ofTicket (T:=T) port header).hardware := by
  have rate := ticket.sourceRate
  subst u
  have same : T = src.placement.stage := eq_of_heq ticket.placement
  cases same
  exact ⟨rfl,rfl,rfl⟩

end Meter
end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage.Dated

end OAI
