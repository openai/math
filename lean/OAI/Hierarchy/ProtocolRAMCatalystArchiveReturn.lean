import OAI.Hierarchy.ProtocolRAMCatalystArchiveVerdict
import OAI.Hierarchy.ProtocolRAMMachine

namespace OAI
/-! # Native machine return for the funded chronological reserve controller -/

noncomputable section
namespace Hierarchy.ProtocolRAM.CatalystArchive
open Calendar Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native AdaptiveProbe
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing Classical
variable {w q goods r edges count payload : ℕ} {I J : Type*} [Fintype I] [Fintype J]
    {core : I→List (Fin edges)} {center : J→List (Fin edges)}

omit [Fintype I] [Fintype J] in
/-- Starting from the mounted calendar, the machine returns the external flag
in the routed report memory. Its two extra steps load the flag address and
read the flag word before returning. -/
theorem terminal_return
    (C : Chart w q goods) (L : OwnerLedger) (routes : List Pass) (flag : ℕ) (s : Sink r edges)
    (src : ℕ) (ss : List PaidWidths.Slice) (a : ReserveUse.Archive) (issued : Attempt→Entry count payload)
    (pos : 0<count) (routeFits : ∀p∈routes,p.Fits w) (enum : Fin r≃RouteOccurrence core center)
    (ci : I→ℕ) (cj : J→Fin count) (origin : Memory w) (state : Word w)
    (active : mounted C (events C.mesh) origin) (order : separated C (events C.mesh))
    (flagFit : (historyFlag C (events C.mesh)).Fits w flag) (flagEnd : flag+1<2^w)
    (width : s.banks.width.base+edges<2^w) (rows : ∀e∈events C.mesh,L.rows e≤L.arena.stride)
    (inputs : ∀e∈events C.mesh,(L.term e).Fits w L.arena.first) (ownerRoom : L.arena.endAddress C.mesh<2^w)
    (routeLow : ∀p∈routes,flag<p.out)
    (below : flag<L.arena.first ∧ flag<s.banks.reserved.base ∧ flag<s.banks.used.base ∧ flag<a.scratch ∧
      flag<s.banks.width.base ∧ flag<s.table ∧ flag<s.destination) :
    let n:=recordCount C.mesh issued
    let supply:=fuel C.mesh*payload
    let tail:=terminal C L routes flag s src ss a count n supply
    let price:=terminalTime C L routes s ss a count n supply
    let chk:=checkedOut C flag origin
    let cash:=PaidWidths.output s.banks.width edges src ss chk
    let archive:=result routes (result (L.scans C.mesh count) cash)
    let owner:=nativeSite L C.mesh issued pos chk
    let debitWord:=debit C.mesh issued
    let out:=s.output (ReserveUse.output a s.banks supply owner debitWord archive) enum ci (fun j=>(cj j).val)
    let cpu:=machine tail (flag:Word w)
    PaidWidths.Mounted s.banks.width edges src ss chk →
    Whole.Reconciliation s a supply owner debitWord enum ci cj archive →
    ∃ t ≤ price+2, ∃ done,
      advance cpu.program t (cpu.program.start state) origin=some (done,out) ∧
      cpu.program.step done=.finish (some (out flag)) ∧
      (out flag=0 ↔ Calendar.admissible C (events C.mesh) origin) := by
  intro n supply tail price chk cash archive owner debitWord out cpu paid settled
  have run : tail.Exec origin out price :=
    terminal_exec C L routes flag s src ss a issued pos routeFits enum ci cj origin
      active flagFit flagEnd width rows inputs ownerRoom paid settled
  obtain ⟨t,ht,done,advance,halt⟩ := machine_run tail (flag:Word w) state origin out price run
  have fit : flag < 2^w := by omega
  have positive : 0 < w := by
    by_contra! h
    have hz : w=0 := by omega
    simp [hz] at flagEnd
  exact ⟨t,ht,done,advance,by simpa only [Fin.val_cast_of_lt fit] using halt,
    terminal_verdict C L routes flag s src ss a issued pos enum ci cj origin active order positive
      paid settled.ports.width routeLow below⟩

end Hierarchy.ProtocolRAM.CatalystArchive
end

end OAI
