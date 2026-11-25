import OAI.Computability.BorderVNP.RoutingISATypedBatchMemory
import OAI.Computability.BorderVNP.RoutingISAAddressProof

/-! # Loading the typed argument directory from the live evaluator frame

Slot 30 gives the word width. Slots 89 and 90 hold this team's task array and
its current row count. A zero count falls through without calling a cell writer.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.TypedBatch

open VPVNP.BurstRAM

/-- Fetch the three physical frame operands before any task-array access. -/
def loadDirectory : Code := .block [
  readFrame 40 62 63 30, readFrame 41 62 63 89, readFrame 42 62 63 90]

/-- The native argument-preparation stage on the common evaluator ABI. -/
def entry : Code := .seq loadDirectory scan

/-- The ABI loader visits the actual shared frame and leaves every other word intact. -/
theorem loadDirectory_run {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (fits : (pub 0).val+90 < 2^w) :
    ∃ es t, Runs pub macros loadDirectory s m es t m ∧ traceCost es ≤ loadDirectory.slots ∧
      (t 40).val=(m ((pub 0).val+30)).val ∧ (t 41).val=(m ((pub 0).val+89)).val ∧
      (t 42).val=(m ((pub 0).val+90)).val := by
  have safe : loadDirectory.safeReadOnly w (readings pub) (readings m) (readings s) := by
    simp (config := {decide := true}) [loadDirectory,readFrame,Code.block,Code.safeReadOnly,Code.evalNat,
      addressOp,addressOpFits,readings]
    omega
  obtain ⟨es,t,run,cost,h⟩ := loadDirectory.runReadOnly pub macros m s safe
  refine ⟨es,t,run,cost,?_⟩
  change readings t 40=_ ∧ readings t 41=_ ∧ readings t 42=_
  rw [h]
  simp (config := {decide := true}) [loadDirectory,Code.block,readFrame,Code.evalNat,addressOp,readings]

/-- On a populated, allocated task table, the real ABI entry writes every packed
argument and publishes its start and length to the associated owner row. -/
theorem entry_run {w table count : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (tasks : ℕ → Task) (frame : (pub 0).val+90 < 2^w)
    (width : (m ((pub 0).val+30)).val=w) (base : (m ((pub 0).val+89)).val=table)
    (len : (m ((pub 0).val+90)).val=count) (space : table+7*count ≤ 2^w)
    (layout : Allocated w table count tasks)
    (source : ∀ i < count, (tasks i).Stored m table i ∧ (tasks i).cell.Stored m)
    (room : ∀ i < count, (tasks i).callRow+2 < 2^w ∧ (tasks i).cell.Room w) :
    ∃ es t, Runs pub macros entry s m es t (written m tasks count) ∧
      traceCost es ≤ loadDirectory.slots+setup.slots+(∑ j ∈ Finset.range count, rowCharge (fun k => (tasks k).cell.cost w) j)+1 ∧
      Ready table count count t := by
  obtain ⟨gs,u,r,h,hw,hb,hl⟩ := loadDirectory_run pub macros s m frame
  have rows := layout.live m source
  obtain ⟨fs,z,next,hn,hz⟩ := scan_run (pub := pub) (macros := macros) u m tasks (by omega)
    (hw.trans width) (hb.trans base) (hl.trans len) space (fun i hi =>
      ⟨(rows i hi).1,(room i hi).1,(rows i hi).2,(room i hi).2⟩)
  refine ⟨_,z,r.seq next,?_,hz⟩
  rw [show traceCost (gs++fs) = traceCost gs+traceCost fs from VPVNP.RAMBuckets.cost_append ..]
  omega

end RoutingISA.TypedBatch

end BorderVNP
end Computability
end OAI
