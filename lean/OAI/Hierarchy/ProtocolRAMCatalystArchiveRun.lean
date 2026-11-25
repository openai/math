import OAI.Hierarchy.ProtocolRAMRowText
import OAI.Hierarchy.ProtocolRAMNativePaidReporter
import OAI.Hierarchy.ProtocolRAMCatalystArchiveTerminal

namespace OAI
/-! # Executing the terminal owner scans, reserve scatter and routing reporter -/

noncomputable section
namespace Hierarchy.ProtocolRAM.CatalystArchive
open Calendar Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native AdaptiveProbe
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing BigOperators Classical
variable {w count payload q goods r edges : ℕ} {I J : Type*} [Fintype I] [Fintype J]
    {core : I→List (Fin edges)} {center : J→List (Fin edges)}

def terminal (C : Chart w q goods) (L : OwnerLedger) (routes : List Pass) (flag : ℕ) (s : Sink r edges) (src : ℕ)
    (ss : List PaidWidths.Slice) (a : ReserveUse.Archive) (count n reserve : ℕ) : Procedure w :=
  (((((checked C flag).seq (PaidWidths.native w edges src s.banks.width ss)).seq
    (program w (L.scans C.mesh count))).seq (program w routes)).seq (ReserveUse.native w a s.banks count n reserve)).seq (s.native w)

def terminalTime (C : Chart w q goods) (L : OwnerLedger) (routes : List Pass) (s : Sink r edges) (ss : List PaidWidths.Slice)
    (a : ReserveUse.Archive) (count n reserve : ℕ) :=
  checkedCost C+PaidWidths.clock s.banks.width edges ss+clock (L.scans C.mesh count)+clock routes+
    ReserveUse.clock a s.banks count n reserve+s.clock

theorem terminal_cheap (C : Chart w q goods) (L : OwnerLedger) (routes : List Pass) (flag : ℕ) (s : Sink r edges)
    (src : ℕ) (ss : List PaidWidths.Slice) (a : ReserveUse.Archive) (count n reserve : ℕ) :
    CheapCode (terminal C L routes flag s src ss a count n reserve) :=
  @cheap_seq w _ (s.native w)
    (@cheap_seq w _ (ReserveUse.native w a s.banks count n reserve)
      (@cheap_seq w _ (program w routes)
        (@cheap_seq w _ (program w (L.scans C.mesh count))
          (@cheap_seq w (checked C flag) (PaidWidths.native w edges src s.banks.width ss)
            (@checked_cheap w q goods C flag) (@PaidWidths.cheap w edges src s.banks.width ss))
          (@program_cheap w (L.scans C.mesh count))) (@program_cheap w routes))
      (@ReserveUse.cheap w a s.banks count n reserve))
    (@RouteSettlement.reporter_cheap w s.source s.table s.destination edges r s.banks s.owners s.geometry)

omit [Fintype I] [Fintype J] in
theorem terminal_exec (C : Chart w q goods) (L : OwnerLedger) (routes : List Pass) (flag : ℕ) (s : Sink r edges)
    (src : ℕ) (ss : List PaidWidths.Slice) (a : ReserveUse.Archive) (issued : Attempt→Entry count payload)
    (pos : 0<count) (routeFits : ∀p∈routes,p.Fits w) (enum : Fin r≃RouteOccurrence core center) (ci : I→ℕ) (cj : J→Fin count)
    (m : Memory w) (mounted : Calendar.mounted C (events C.mesh) m)
    (flagFit : (historyFlag C (events C.mesh)).Fits w flag) (flagEnd : flag+1<2^w)
    (width : s.banks.width.base+edges<2^w) (rows : ∀e∈events C.mesh,L.rows e≤L.arena.stride)
    (inputs : ∀e∈events C.mesh,(L.term e).Fits w L.arena.first) (ownerRoom : L.arena.endAddress C.mesh<2^w) :
    let chk := checkedOut C flag m
    let paid := PaidWidths.output s.banks.width edges src ss chk
    let archive := result routes (result (L.scans C.mesh count) paid)
    let owner := nativeSite L C.mesh issued pos chk
    let debitWord := debit C.mesh issued
    let supply := fuel C.mesh*payload
    let committed := ReserveUse.output a s.banks supply owner debitWord archive
    PaidWidths.Mounted s.banks.width edges src ss chk →
    Whole.Reconciliation s a supply owner debitWord enum ci cj archive →
    (terminal C L routes flag s src ss a count (recordCount C.mesh issued) supply).Exec m
      (s.output committed enum ci (fun z=>(cj z).val)) (terminalTime C L routes s ss a count (recordCount C.mesh issued) supply) := by
  intro chk paid archive owner debitWord supply committed paidFit settled
  unfold terminal terminalTime
  apply Procedure.Exec.then (b:=committed)
  · apply Procedure.Exec.then (b:=archive)
    · apply Procedure.Exec.then (b:=result (L.scans C.mesh count) paid)
      · apply Procedure.Exec.then (b:=paid)
        · exact Procedure.Exec.then (b:=chk) (checked_exec C flag m mounted flagFit flagEnd)
            (PaidWidths.exec s.banks.width src ss chk width paidFit)
        · exact L.execute C.mesh count paid rows inputs ownerRoom
      · exact program_exec routes _ routeFits
    · exact ReserveUse.exec a s.banks supply owner debitWord archive settled.archive
  · exact s.exec committed enum ci (fun z=>(cj z).val)
      (settled.ports.mounted a supply owner debitWord settled.archive settled.usedSize settled.reserveSize settled.funded settled.word)

theorem terminal_text (C : Chart w q goods) (L : OwnerLedger) (routes : List Pass) (flag : ℕ)
    (s : Sink r edges) (src : ℕ) (ss : List PaidWidths.Slice) (a : ReserveUse.Archive) (count n reserve : ℕ) :
    text (terminal C L routes flag s src ss a count n reserve)=
      text (paidReporter C flag s src ss a count n reserve)+listText (L.scans C.mesh count)+listText routes := by
  simp only [terminal,paidReporter,text_seq,text_passes]
  omega

end Hierarchy.ProtocolRAM.CatalystArchive
end

end OAI
