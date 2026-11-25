import OAI.ThreeFlat.RAM.PhysicalProcedureSize
import OAI.ThreeFlat.RAM.PhysicalInputPhases
import OAI.ThreeFlat.RAM.PhysicalProcedureIf
import OAI.ThreeFlat.RAM.HistoryReadyTape
import OAI.ThreeFlat.RAM.HistorySelectedProcedure

namespace OAI
/-! # Resource counts for native writes, tapes, conditionals and selected-node guards -/
namespace ThreeFlat.RAM.HistoryStageBody.Physical
open Computability.VPVNP.BurstRAM PhysicalProcedure PhysicalPinsExpr DescriptorExpr
open scoped Classical BigOperators Fin.CommRing
noncomputable section

theorem resources_write {W k : ℕ} (t : Term W k 1) (pub : Fin k→Word W) (addr len : ℕ) :
    resources (PhysicalInputPhases.writing t pub addr len)=11+4*t.binds+k := by
  dsimp only [resources,PhysicalInputPhases.writing]
  rw [t.labels_eq];omega

theorem resources_tape {W k : ℕ} (t : Term W k 1) (base : Fin k) (pub : Fin k→Word W) :
    resources (HistoryReadyTape.execute t base pub)=29+4*t.binds+k := by
  dsimp only [resources,HistoryReadyTape.execute]
  rw [t.labels_eq];omega

theorem resources_if {W : ℕ} (f : Formula 1) (yes no : Procedure W) :
    resources (ifValue f yes no)=(6+4*f.work)+resources yes+resources no := by
  change (3+(3*f.work+1)+(yes.labels+no.labels))+(2+f.work+(yes.registers+no.registers))+
      (yes.slots+no.slots)=(6+4*f.work)+(yes.labels+yes.registers+yes.slots)+(no.labels+no.registers+no.slots)
  omega

theorem resources_guard {W : ℕ} (data : HistoryNodeDirectory.Selected.Data W) (p : Procedure W) :
    resources (HistoryNodeDirectory.Selected.procedure data p)=49+resources p := by
  change 35+p.labels+(8+p.registers)+(6+p.slots)=49+(p.labels+p.registers+p.slots)
  omega


end
end ThreeFlat.RAM.HistoryStageBody.Physical

end OAI
