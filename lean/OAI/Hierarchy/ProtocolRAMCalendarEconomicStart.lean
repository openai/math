import OAI.Hierarchy.ProtocolRAMCoreRouteImage
import OAI.Hierarchy.ProtocolRAMCalendarEconomicBootFrame
import OAI.Hierarchy.ProtocolRAMCalendarEconomicFits

namespace OAI
/-! # Executing the joint subdivision startup for the reporting board and the adaptive account -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CoreRoute
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage CoreBoard ReportSockets BoughtSockets CatalogueRows StripChart
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
variable {z W k attempts R K H jobs phases X Y steps : ℕ} {S : PurchaseSampler}

theorem economic_start (E : EconomicHeader phases X Y steps) (ordered : E.Ordered)
    (order : Fin R≃Edges S z (2^W) k) (M : ℕ) (groups : Fin K≃AllGroups z (2^W))
    (packed : TaggedShorterSupergroups.Directory (TaggedShorterSupergroups.reserved z W (copies k attempts)) H)
    (joint : JointHeader.Board) (N depth : ℕ) (phase : Fin phases→PhasePrice)
    (π : Equiv.Perm (Fin (2^z))) (stock : ℕ→ℕ) (rest : Boot.Tape z (2^W))
    (markets : Fin jobs→Market z (2^W) k) {size : ℕ} (layout : Boot.Layout markets size) (v : Directory attempts)
    (positive : 0<phases) (room : E.stop<2^Native.wordBits z (2^W) Native.copies)
    (before : ∀i,E.stop≤Boot.low (markets i)) (within : E.stop≤ size)
    (first : 2^z≤joint.initial) (afterScore : JointHeader.stop joint z N k phases≤E.ports.base)
    (afterCT : Native.heapEnd z (2^W) Native.copies≤E.ports.base)
    (base : stop S z W k attempts depth K packed.groups H R≤joint.initial)
    (portAfter : stop S z W k attempts depth K packed.groups H R≤E.ports.base) :
    let input:=E.scalar.words (E.vectorMemory rest)
    let lowData:=low order M groups packed depth input
    let words:=JointHeader.words joint z (2^W) N k phase π stock (E.ports.words lowData)
    let mid:=Boot.booted markets size words
    (Native.subdivisionProgram z (2^W)).Exec (Boot.initial markets size words) mid (Native.subdivisionConstant (2^W)*2^z) ∧
      Boot.Receipt markets π (Computability.VPVNP.RAMMemory.initialMemory size words) mid ∧
      Seen order M groups packed v depth π mid ∧ E.Resident mid := by
  intro input lowData words mid
  have lower : stop S z W k attempts depth K packed.groups H R≤E.scalar.base :=
    portAfter.trans ((Nat.le_add_right ..).trans ordered.scalarBase.le)
  have upper : E.scalar.base≤E.stop:=by
    have a : E.scalar.base≤E.scalar.stop:=Nat.le_add_right ..
    have u : E.payload.base≤E.payload.stop:=Nat.le_add_right ..
    have b : E.bought.base≤E.bought.stop:=Nat.le_add_right ..
    have m:=EconomicHeader.Ordered.menu_bounds E ordered
    have t : E.payloadTree.base≤E.payloadTree.stop:=Nat.le_add_right ..
    have f : E.boughtTree.base≤E.stop:=Nat.le_add_right ..
    rcases ordered with ⟨_,o₂,o₃,o₄,_,o₅,o₆⟩
    omega
  have core:=start order M groups packed joint E.ports N depth phase π stock input markets layout v
    ⟨base,portAfter,(lower.trans upper).trans within,(lower.trans upper).trans_lt room,
      fun i=>(lower.trans upper).trans (before i)⟩
  have receipts:=E.origin_with_low ordered joint phase π stock rest markets layout Nat.one_le_two_pow first
    afterScore afterCT (E.fits_of_stop ordered positive room.le) room before within (low order M groups packed depth)
    (fun m x hx=>low_above order M groups packed depth m x (lower.trans hx))
  exact ⟨core.1,core.2.1,core.2.2,receipts⟩

end Hierarchy.ProtocolRAM.Calendar.CoreRoute
end

end OAI
