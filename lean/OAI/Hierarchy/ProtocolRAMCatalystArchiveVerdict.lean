import OAI.Hierarchy.ProtocolRAMCatalystArchiveRun
import OAI.Hierarchy.ProtocolRAMNativeReserveFrame

namespace OAI
/-! # The final routed decision word of the chronological reserve controller -/

noncomputable section
namespace Hierarchy.ProtocolRAM.CatalystArchive
open Calendar Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native AdaptiveProbe
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing Classical

section Reporter
variable {w q goods r edges count payload : ℕ} {I J : Type*} [Fintype I] [Fintype J]
    {core : I→List (Fin edges)} {center : J→List (Fin edges)}

/-- The signed entries only certify the time-indexed widths and owners. The
whole terminal code and its exact budget can instead use the fixed public
number of padded records, even when the calendar is empty. -/
theorem terminal_rowOnly (C : Chart w q goods) (L : OwnerLedger) (routes : List Pass)
    (flag : ℕ) (s : Sink r edges) (src : ℕ) (ss : List PaidWidths.Slice) (a : ReserveUse.Archive)
    (issued : Attempt→Entry count payload) (rows : Attempt→ℕ) (same : ∀ t,(issued t).rows=rows t) :
    let n:=recordCount C.mesh issued
    let m:=rowOnlyCount C.mesh rows
    let reserve:=fuel C.mesh*payload
    terminal C L routes flag s src ss a count n reserve=terminal C L routes flag s src ss a count m reserve ∧
      terminalTime C L routes s ss a count n reserve=terminalTime C L routes s ss a count m reserve := by
  dsimp only
  constructor <;> rw [recordCount_rowOnly C.mesh issued rows same]

omit [Fintype I] [Fintype J] in
/-- The four post-verdict native scans read or write only their own physical
slabs. Consequently their final machine flag tests the original chart verdict. -/
theorem terminal_verdict (C : Chart w q goods) (L : OwnerLedger) (routes : List Pass) (flag : ℕ) (s : Sink r edges)
    (src : ℕ) (ss : List PaidWidths.Slice) (a : ReserveUse.Archive) (issued : Attempt→Entry count payload)
    (pos : 0<count) (enum : Fin r≃RouteOccurrence core center) (ci : I→ℕ) (cj : J→Fin count)
    (m : Memory w) (active : mounted C (events C.mesh) m) (order : separated C (events C.mesh))
    (width : 0<w) (paid : PaidWidths.Mounted s.banks.width edges src ss (checkedOut C flag m))
    (stockEnd : s.banks.width.base+edges≤ s.source) (routeLow : ∀p∈routes,flag<p.out)
    (below : flag<L.arena.first ∧ flag<s.banks.reserved.base ∧ flag<s.banks.used.base ∧ flag<a.scratch ∧
      flag<s.banks.width.base ∧ flag<s.table ∧ flag<s.destination) :
    let chk:=checkedOut C flag m
    let cash:=PaidWidths.output s.banks.width edges src ss chk
    let archive:=result routes (result (L.scans C.mesh count) cash)
    let committed:=ReserveUse.output a s.banks (fuel C.mesh*payload) (nativeSite L C.mesh issued pos chk)
      (debit C.mesh issued) archive
    s.output committed enum ci (fun j=>(cj j).val) flag=0 ↔ Calendar.admissible C (events C.mesh) m := by
  intro chk cash archive committed
  obtain ⟨owners,res,used,scr,stock,tab,dest⟩:=below
  rw [s.frame _ _ _ _ _ stock tab dest stockEnd]
  change ReserveUse.output _ _ _ _ _ archive flag=0 ↔ _
  rw [ReserveUse.frame _ _ _ _ _ _ _ (.inl res) (.inl used) (.inl scr)]
  change result routes (result (L.scans C.mesh count) cash) flag=0 ↔ _
  rw [result_below _ _ flag routeLow]
  rw [L.before C.mesh count cash flag owners]
  change PaidWidths.output s.banks.width edges src ss chk flag=0 ↔ _
  rw [PaidWidths.frame _ _ _ _ _ _ (fun j hj=>(paid j hj).1) stock]
  exact checked_read C flag m active order width

end Reporter

end Hierarchy.ProtocolRAM.CatalystArchive
end

end OAI
