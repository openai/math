import OAI.Hierarchy.DescentDatedOrdinaryAny
import OAI.Hierarchy.DescentDatedOrdinaryHardware
import OAI.Hierarchy.DescentPrivateNativePhase
import OAI.Hierarchy.DescentTerminalExecUnique

namespace OAI
/-! # The uniquely determined memory at the end of the public ordinary-date program -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage.Dated.Ordinary
open DescentSixParty Chronology ProtocolRAM Computability.VPVNP.BurstRAM
open ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable {F : Type} [Field F] (a : Ordinary) (gadget : PoweredGadget F) (hk : 0<a.k)
  (ports : Operands) (v : Measures) (w base : ℕ) (fit : a.Space ports w base)

def nativePhase : NativePhase w where
  program:=a.program gadget hk ports v w base
  ticks:=a.ticks gadget hk ports v w base
  image:=fun m=>(a.any ports w base gadget hk v fit m).choose
  cheap:=@cheap F _ a gadget hk ports v w base

theorem nativePhase_all (m : Memory w) :
    (a.nativePhase gadget hk ports v w base fit).Runs m :=
  (a.any ports w base gadget hk v fit m).choose_spec

/-- The memory read by the next date is the precise state in the true geometric
certificate. An existentially supplied valid execution cannot choose another state. -/
theorem nativePhase_issued (m physical : Memory w) {time : ℕ}
    (observed : (a.program gadget hk ports v w base).Exec m physical time) :
    (a.nativePhase gadget hk ports v w base fit).image m=physical :=
  exec_unique _ m _ physical (a.nativePhase_all gadget hk ports v w base fit m) observed

theorem nativePhase_report (m : Memory w) {time : ℕ} (R : Memory w→Prop)
    (issued : ∃out,(a.program gadget hk ports v w base).Exec m out time ∧ R out) :
    R ((a.nativePhase gadget hk ports v w base fit).image m) :=
  actual_after _ m _ (a.nativePhase_all gadget hk ports v w base fit m) issued

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage.Dated.Ordinary

end OAI
